#include <stdio.h>
#include <math.h>
#include "DWArith.h"

int main(void) {
    dword st = {0.0,0.0};
    dword x  = {1.0,0.0};
    float a = 1.0;
    SDWPFP (&st, &x, a);
    printf("%1.16g\n",st.s);
    printf("%1.16g\n",st.t);
    return 0;
}
