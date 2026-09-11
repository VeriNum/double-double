# FenceDD C Library

The C layer provides error-free transformations and double-word addition,
multiplication, and division. The public declarations are in
[`include/dw_arith.h`](include/dw_arith.h).

Public wrappers return a `dw_status` and update the output only when they return
`DW_OK`. Composite operations provide a default wrapper, which checks a weak
condition on the operands and the returned value, and a `_strong` wrapper,
which checks a stronger condition on the operands before running the kernel.
The motivation for these checks and their precise definitions are described in
the FenceDD paper. Functions ending in `_kernel` are the arithmetic implementations
used by the wrappers.

Run `make -C dd_lib` from the repository root to build `libfencedd.a` and the
example program with CompCert. Run the example with:

```sh
./dd_lib/example
```

For the numerical theorems and the VST proofs attached to each interface, see
the [guide to the Rocq layer](../FenceDD_Rocq_Guide.md).
