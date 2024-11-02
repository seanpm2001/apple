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

TS apple_t {enum apple_at sa; enum apple_at aa; struct apple_t* a_pi;} apple_t;

TS FnTy {int argc; apple_t* args; apple_t res;} FnTy;

Z void freety(FnTy* x){free(x->args);free(x);}

// NULL on error
FnTy* apple_ty(K char*, T*);
