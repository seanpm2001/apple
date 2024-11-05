#include<stdlib.h>
#include<math.h>
#include<ffi.h>
#include"../include/apple.h"

#define G static const
#define SZ sizeof
// https://github.com/tlack/b-decoded/blob/3c21a33a5c3f5d39f75014e10f875fe830a8b326/orig-files/c.h#L8
#define SA(t,x) t* x=alloca(SZ(t))
#define $(p,a) if(p){a;}else

#define F(r,t) {$(t.f==Sc,{switch(t.ty.sa){C(I_t,r=&ffi_type_sint64) C(B_t,r=&ffi_type_uint8) C(F_t,r=&ffi_type_double)}}) {r=&ffi_type_pointer;}}

G JC sys={(P)&malloc,(P)&free,(P)&lrand48,(P)&drand48,(P)&exp,(P)&log,(P)&pow};

ffi_cif* apple_ffi(FnTy* ty) {
    ffi_cif* cif=malloc(sizeof(*cif));
    int argc=ty->argc;
    ffi_type** args=malloc(sizeof(ffi_type*)*argc);
    apple_t* argv=ty->args;
    DO(i,argc,F(args[i],argv[i]))
    ffi_type* ret;F(ret,ty->res);
    ffi_prep_cif(cif,FFI_DEFAULT_ABI,(unsigned int)argc,ret,args);
    R cif;
}

#define ArgTy(t,fc,i,b,fa,ia,ba,tup) switch(t.f) {C(Sc,switch(t.ty.sa){C(F_t,fc) C(I_t,i) C(B_t,b)}) C(Aa,switch(t.ty.aa){C(F_t,fa) C(I_t,ia) C(B_t,ba)}) C(Pi,tup)};;
