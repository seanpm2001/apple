#include<sys/mman.h>
#include<R.h>
#include<Rinternals.h>
#include<HsFFI.h>
#include<ffi.h>
#include"../include/apple_abi.h"
#include"../c/ffi.c"

// asReal : SEXP -> double
// asInteger : SEXP -> int
// ScalarReal : double -> SEXP
// ScalarInteger : int -> SEXP
// SEXPTYPE = INTSXP | REALSXP | LGLSXP
// EXTPTR_PTR : SEXP -> void*

// http://adv-r.had.co.nz/C-interface.html

#define ERR(p,msg){if(p==NULL){SEXP er=mkString(msg);free(msg);R er;};}
#define E(msg){SEXP er=mkString(msg);R er;}
#define An(x,n,t,ra) J* i_p=x;J n=i_p[1];SEXP ra=PROTECT(allocVector(t,n));

#define ZR static SEXP

TS AppleC {U code;S code_sz;FnTy* ty;U sa;ffi_cif* ffi;} AppleC;

Z void clear(SEXP jit) {
    AppleC* c=(AppleC*)R_ExternalPtrAddr(jit);
    munmap(c->code,c->code_sz);
    free(c->sa);free(c->ffi);freety(c->ty);
}

ZR rfv(U x) {An(x,n,REALSXP,r);F* x_f=x;memcpy(REAL(r),x_f+2,n*8);UNPROTECT(1);R r;}
ZR ri(U x) {An(x,n,INTSXP,r);DO(i,n,INTEGER(r)[i]=(int)i_p[i+2]);UNPROTECT(1);R r;}
ZR rb(U x) {An(x,n,LGLSXP,r);B* b_p=x+16;DO(i,n,LOGICAL(r)[i]=(int)b_p[i]);UNPROTECT(1);R r;}

// vector only
ZU frv(SEXP x) {J dim=length(x);double* d=REAL(x);V(dim,d,ret);R ret;}
ZU fi(SEXP x) {J dim=length(x);J* ret=R_alloc(8,dim+2);J rnk=1;ret[0]=rnk;ret[1]=dim;DO(i,dim,ret[i+2]=(J)(INTEGER(x)[i]));R ret;}
ZU fb(SEXP x) {J dim=length(x);B* ret=R_alloc(1,dim+16);J* i_p=(J*)ret;J rnk=1;i_p[0]=rnk;i_p[1]=dim;DO(i,dim,ret[i+16]=(B)(LOGICAL(x)[i]));R ret;}

ZU frm(SEXP a) {int* ds=INTEGER(getAttrib(a,R_DimSymbol));J m=ds[0];J n=ds[1];U x=malloc(24+m*n*8);J* x_i=x;x_i[0]=2;x_i[1]=m;x_i[2]=n;F* x_f=x;double* d=REAL(a);DO(i,m,(DO(j,n,x_f[i*n+j+3]=d[j*m+i])));R x;}
ZR rfm(U x) {J* i_p=x;J m=i_p[1],n=i_p[2];F* x_f=x;SEXP r=PROTECT(allocMatrix(REALSXP,m,n));double* d=REAL(r);DO(i,m,DO(j,n,d[j*m+i]=x_f[i*n+j+3]));UNPROTECT(1);R r;}

ZU fr(SEXP a){if(Rf_isMatrix(a)){R frm(a);}else if (Rf_isVector(a)){R frv(a);}else E("Higher-rank arguments not supported.")}
ZR rf(U x){J* x_i=x;J rnk=x_i[0];if(rnk==1){R rfv(x);}else if(rnk==2){R rfm(x);}else E("Higher-rank return values are not supported.")}

SEXP hs_init_R(void) {
    hs_init(0,0);
    R mkString("...loaded GHC runtime");
}

SEXP ty_R(SEXP a) {
    K char* inp=CHAR(asChar(a));T err;
    T typ=apple_printty(inp,&err);
    ERR(typ,err);
    R mkString(typ);
}

SEXP jit_R(SEXP a){
    K char* inp=CHAR(asChar(a));
    T err;
        FnTy* ty=apple_ty(inp,&err);
    ERR(ty,err);
    S f_sz;U s;
    U fp=apple_compile(&sys,inp,&f_sz,&s);
    AppleC* rc=malloc(SZ(AppleC));
    ffi_cif* ffi=apple_ffi(ty);
    rc->code=fp;rc->code_sz=f_sz;rc->ty=ty;rc->sa=s;rc->ffi=ffi;
    // http://homepage.divms.uiowa.edu/~luke/R/simpleref.html#toc6
    // https://github.com/hadley/r-internals/blob/master/external-pointers.md
    SEXP r=R_MakeExternalPtr((U)rc,R_NilValue,R_NilValue);
    R_RegisterCFinalizer(r,&clear);
    R r;
}

SEXP asm_R(SEXP a) {
    K char* inp=CHAR(asChar(a));T err;
    T ret=apple_dumpasm(inp,&err);
    ERR(ret,err);
    R mkString(ret);
}

SEXP run_R(SEXP args){
    args=CDR(args);
    SEXP rc=CAR(args);
    AppleC* c=(AppleC*)(R_ExternalPtrAddr(rc));
    FnTy* ty=c->ty;U fp=c->code;ffi_cif* cif=c->ffi;
    SEXP r;
    int argc=ty->argc;
    U* vals=alloca(SZ(U)*argc), ret=alloca(8);
    uint8_t fs=0;
    for(int k=0;k<argc;k++){
        args=CDR(args);SEXP arg=CAR(args);
        switch(ty->args[k]){
            C(FA,SA(U,x);*x=fr(arg);fs|=1<<k;vals[k]=x;)
            C(IA,SA(U,x);*x=fi(arg);vals[k]=x;)
            C(BA,SA(U,x);*x=fb(arg);vals[k]=x;)
            C(F_t,SA(F,xf);*xf=asReal(arg);vals[k]=xf;)
            C(I_t,SA(J,xi);*xi=(J)asInteger(arg);vals[k]=xi;)
            C(B_t,SA(B,xb);*xb=(B)asLogical(arg);vals[k]=xb;)
        }
    }
    ffi_call(cif,fp,ret,vals);
    DO(i,argc,if(fs>>i&1){free(*(U*)vals[i]);})
    switch(ty->res){
        C(FA,r=rf(*(U*)ret))
        C(IA,r=ri(*(U*)ret))
        C(BA,r=rb(*(U*)ret))
        C(F_t,r=ScalarReal(*(F*)ret))
        C(I_t,r=ScalarInteger((int)(*(J*)ret)))
        C(B_t,r=ScalarLogical(*(int*)ret))
    }
    R r;
}
