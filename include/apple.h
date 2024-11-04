#include"m.h"
#define K const

// exp, log, pow can be NULL on X86
TS JC {P ma; P free;P r;P xr;P e;P log;P pow;} JC;

U apple_compile(K JC*,K char*,S*,U*);

// NULL on error
// first argument: source
// second argument: error return
T apple_printty(K char*, T*);
T apple_dumpasm(K char*, T*);
T apple_x86(K char*, T*);
T apple_aarch64(K char*, T*);
T apple_dumpir(K char*, T*);
T apple_print_ts_sz(K char*, S*, T*);

enum apple_at{I_t=1,F_t=2,B_t=3};

enum HK{Sc,Aa,Pi};

TS apple_Pi{int pi_n; struct apple_t* a_pi;} apple_Pi;

// hm https://stackoverflow.com/questions/20752551/working-with-a-union-of-structs-in-c
TS apple_t {enum HK f; union {enum apple_at sa; enum apple_at aa; struct apple_Pi APi;} ty;} apple_t;

TS FnTy {int argc; apple_t* args; apple_t res;} FnTy;

_ void free_t(apple_t x){if(x.f==Pi){apple_Pi p=x.ty.APi;DO(j,p.pi_n,free_t(*p.a_pi));free(p.a_pi);}}

_ void freety(FnTy* x){DO(i,x->argc,free_t(x->args[i]));free(x->args);free_t(x->res);free(x);}

// NULL on error
FnTy* apple_ty(K char*, T*);
