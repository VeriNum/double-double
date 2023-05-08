#include <stdio.h>
#include <math.h>
#include "dw_arith.h"

int main(void) {
    struct dword EPS = {0.0,0.0};
    struct dword EPS1 = {0.0,0.0};
    struct dword EPS2 = {0.0,0.0};
    struct dword EPS3 = {0.0,0.0};
    struct dword one = {1.0,0.0};
    struct dword four= {-4.0,0.0};
    struct dword three = {3.0,0.0};
    double t = 3.0;
    dw_div_fp15(&EPS1,&four,t);
    dw_plus_dw2(&EPS2,&one,&EPS1);
    dw_mult_dw12(&EPS3,&three,&EPS2);
    dw_plus_dw2(&EPS,&one,&EPS3);
    printf("%1.16g\n",EPS.s);
    printf("%1.16g\n",EPS.t);
    return 0;
}
