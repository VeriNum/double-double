# FenceDD

FenceDD is a verified C library for double-word arithmetic over IEEE 754
floating-point formats. The Rocq development proves numerical properties of
the functional models of double-word algorithms and their building blocks.
VST connects those models to the C implementations.

## Proof architecture

FenceDD builds on the FLX analysis developed by Jean-Michel Muller and
Laurence Rideau in [*Formalization of Double-Word Arithmetic, and Comments on
"Tight and Rigorous Error Bounds for Basic Building Blocks of Double-Word
Arithmetic"*](https://doi.org/10.1145/3484514). That work mechanizes and
refines the analyses introduced by Mioara Joldes, Jean-Michel Muller, and
Valentina Popescu in [*Tight and Rigorous Error Bounds for Basic Building
Blocks of Double-Word Arithmetic*](https://doi.org/10.1145/3121432).

`FLX_analysis/` contains the adapted Rocq development for the fixed-precision,
unbounded-exponent FLX format in Flocq. FenceDD connects those results to
bounded IEEE 754 models, proves guarantees that account for underflow and
overflow, and verifies the C implementations with VST.

```text
FLX_analysis
      ↓
common + DDModels.v + DDConds.v
      ↓
accuracy_proofs
      ↓
verif_proofs ↔ fenceDD
```

## Repository layout

| Path | Contents |
|---|---|
| [`FLX_analysis/`](FLX_analysis/) | Adapted Muller-Rideau FLX analysis and its separate license |
| [`common/`](common/) | Shared rounding lemmas, FLX-to-FLT bridges, and tactics |
| [`DDModels.v`](DDModels.v), [`DDConds.v`](DDConds.v), [`DWord_defs.v`](DWord_defs.v) | Functional models, theorem hypotheses, and connections between the FLX and FenceDD definitions |
| [`accuracy_proofs/basic_blocks/`](accuracy_proofs/basic_blocks/) | Results for TwoSum, Fast2Sum, and Fast2Mult |
| [`accuracy_proofs/dw_opps/`](accuracy_proofs/dw_opps/) | Accuracy and double-word results for composite operations |
| [`fenceDD/`](fenceDD/) | C kernels, runtime checks, public wrappers, header, and example |
| [`verif_proofs/`](verif_proofs/) | Generated Clight models, VST specifications, function proofs, and VSUs |
| [`bench/`](bench/) | Measurement and analysis programs |
| [`paper/`](paper/) | Source and generated material for the FenceDD paper |

## Building the Rocq development

The numerical accuracy development requires Rocq, Flocq, MathComp ssreflect,
and VCFloat. Build that layer without generating Clight models or compiling VST
proofs with:

```sh
make accuracy
```

The C verification additionally requires CompCert, `clightgen`, VST, and
VSTlib. Build the accuracy prerequisites, generate Clight models when needed,
and compile the VST proofs and VSUs with:

```sh
make verification
```

Running `make` also builds the complete Rocq development. To regenerate only
the Clight models, run `make run-clightgen`.

## Documentation

- [Guide to the Rocq layer](FenceDD_Rocq_Guide.md): definitions, functional models,
  numerical theorems, and mappings from numbered results in the paper.
- [C library guide](fenceDD/README.md): public C interfaces, kernels, wrappers,
  and build information.
- [Benchmark guide](bench/README.md): requirements, measurement programs,
  analysis programs, and reproduction commands.
