# FenceDD

FenceDD is a verified C library for double-word arithmetic over IEEE 754
floating-point formats. The Rocq development proves numerical properties of
the functional models of double-word algorithms and their building blocks, and VST connects those models to C implementations.

## Documentation

- [Guide to the Rocq layer](FenceDD_Rocq_Guide.md): definitions, functional models,
  numerical theorems, and mappings from numbered results in the paper.
- [C library guide](dd_lib/README.md): public C interfaces, kernels, wrappers,
  and build information.
- [Benchmark guide](bench/README.md): requirements, measurement programs,
  analysis programs, and reproduction commands.
