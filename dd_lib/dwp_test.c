#include <stdio.h>
#include <math.h>
#include "dw_arith.h"

int main(void) {
    struct dword st = {0.0,0.0};
    struct dword x  = {1.0,0.0};
    float a = 1.0;
    dw_plus_sfp(&st, &x, a);
    printf("%1.16g\n",st.s);
    printf("%1.16g\n",st.t);
    return 0;
}
