#include<stdio.h>
#include<aaf2.h>

int main(int argc, char *argv[]) {
    F xs[] = {0,1,2,3};
    F ys[] = {-1,0.2,0.9,2.1};
    J d[] = {4};
    Af a = {1,d,xs};
    Af b = {1,d,ys};
    F2 res=aaf2_wrapper(a,b);
    printf("%f %f", res.x, res.y);
}
