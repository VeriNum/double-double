#include <stdio.h>
#include <math.h>
#include "dw_arith.h"

int main(void) {
    struct dword st = {0.0,0.0};
    double a = 1.0;
    double b = -1.0;
    fast_2mult(&st, a, b);
    printf("%1.16g\n",st.s);
    printf("%1.16g\n",st.t);
    return 0;
}
