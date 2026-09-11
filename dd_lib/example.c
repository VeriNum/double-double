#include <stdio.h>

#include "dw_arith.h"

int main(void) {
    struct dword x = {1.0, 0x1p-54};
    struct dword y = {2.0, 0x1p-53};
    struct dword result;
    enum dw_status status = dw_plus_dw(&result, &x, &y);

    if (status != DW_OK) {
        fprintf(stderr, "dw_plus_dw failed with status %d\n", status);
        return 1;
    }

    printf("(%a + %a) + (%a + %a) = %a + %a\n",
           x.s, x.t, y.s, y.t, result.s, result.t);
    return 0;
}
