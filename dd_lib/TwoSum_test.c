#include <stdio.h>
#include <math.h>
#include "DWArith.h"

int main(void) {
    dword st = {0.0,0.0};
    double a = 1.0;
    double b = -1 * pow(2,-3*54);
    TwoSum (&st, a, b);
    printf("%1.16g\n",st.s);
    printf("%1.16g\n",st.t);
    return 0;
}
