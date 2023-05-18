#include<stdint.h>
typedef intptr_t P;

void* apple_compile(P,P,const char*,size_t*);

// NULL on error
char* apple_printty(const char*, char**);
char* apple_dumpasm(const char*, char**);
char* apple_x86(const char*, char**);
char* apple_aarch64(const char*, char**);
char* apple_dumpir(const char*, char**);

enum apple_t{I_t,F_t,IA,FA};

typedef struct FnTy {int argc; enum apple_t* args; enum apple_t res;} FnTy;

// NULL on error
FnTy* apple_ty(const char*, char**);
