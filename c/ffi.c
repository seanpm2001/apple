#include<stdlib.h>
#include<ffi.h>
#include"../include/apple.h"

#define R return
#define Sw switch
#define C case

#define DO(i,n,a) {int i;for(i=0;i<n;i++){a;}}

ffi_type ftype(enum apple_t t) {
    Sw(t){
        C I_t: R ffi_type_sint64;
        C F_t: R ffi_type_double;
        C IA: R ffi_type_pointer;
        C FA: R ffi_type_pointer;
    }
}

ffi_cif* apple_ffi(FnTy* ty) {
    ffi_cif* cif=malloc(sizeof(cif));
    int argc=ty->argc;
    ffi_type* args=malloc(sizeof(ffi_type)*argc);
    enum apple_t* argv=ty->args;
    DO(i,argc,args[i]=ftype(argv[i]));
    ffi_type ret=ftype(ty->res);
    ffi_prep_cif(cif,FFI_DEFAULT_ABI,(unsigned int)argc,&ret,&args);
    R cif;
}
