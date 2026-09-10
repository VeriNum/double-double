# Benchmark tools

The benchmark has one measurement path and one analysis path.

- `generate_numerical_data.cpp` records the numerical inputs, wrapper outcomes,
  FenceDD results, and QD results.
- `generate_performance_data.cpp` records every timing trial. It is linked once with
  CompCert objects and once with Clang objects.
- `analyze_rq1.cpp`, `analyze_rq2.cpp`, and `analyze_rq3.cpp` analyze one
  research question each.

The analyzer does not link FenceDD or QD. It cannot execute the measured
implementations. It reads the raw files and writes derived files elsewhere.

## Requirements

The measurement programs require CompCert, Clang, a C++14 compiler, MPFR,
GMP, and QD headers. The analyzer requires only a C++14 compiler, MPFR, and
GMP.

The build obtains MPFR and GMP flags from `pkg-config`. Set `MPFR_CFLAGS` and
`MPFR_LIBS` if they cannot be found that way.

`QD_PREFIX` is required when measurement programs are built. For example:

```sh
make QD_PREFIX=/absolute/path/to/qd all-results RUN_DIR=results/
```

`DD_LIB_DIR` may be used when `dd_lib` is not next to this directory.

## Full run

From this directory, run:

```sh
make QD_PREFIX=/absolute/path/to/qd all-results RUN_DIR=results/
```

This runs the full measurement first and the analysis second. It produces:

```text
results/
  numerical.tsv
  timing-compcert.tsv
  timing-clang.tsv
  analysis/
    rq1.tsv
    rq2.tsv
    rq3.tsv
```

The command does not create a manifest, checksum file, or Git record. The
`results/` directory is ignored by Git.

The raw step refuses to replace an existing raw file. The analysis files are
derived and may be regenerated.

## Separate steps

The same work may be run in two commands:

```sh
make QD_PREFIX=/absolute/path/to/qd raw-results RUN_DIR=results/
make analyze-results RUN_DIR=results/
```

The main workload values are:

```make
SAMPLES_PER_EXPONENT ?= 40
NUM_INPUTS_FOR_PERF ?= 65536
NUM_TRIALS_FOR_PERF ?= 24
```

They may be changed on the command line for a small local run:

```sh
make QD_PREFIX=/absolute/path/to/qd raw-results RUN_DIR=results/ \
  SAMPLES_PER_EXPONENT=1 \
  NUM_INPUTS_FOR_PERF=4096 \
  NUM_TRIALS_FOR_PERF=24
make analyze-results RUN_DIR=results/
```

## Raw numerical data

`numerical.tsv` contains one row for each generated case and each operation.
The three error free transformations share one input set. The three mixed
double word operations share another set. The three double word operations
share a third set.

Each row records:

- the exact input bits;
- the default outcome and returned bits, when it returned;
- the strong outcome and returned bits, when it returned;
- the QD result bits.

The default and strong values are recorded independently. Generation does not
require their outcomes or returned bits to match.

## RQ1 analysis

RQ1 uses the six composite operations. A case is eligible when the default
wrapper returned normally.

The analyzer reconstructs each input and result with MPFR. It computes the
reference, actual error, proved bound, and ratio of error to bound for both
FenceDD and QD.

The relative error is reported when the relative term in the proved bound is
at least as large as the absolute term. The absolute error is reported in the
other regime. A zero bound has its own row.

Means and maxima are explicitly labelled as finite result statistics.
Nonfinite values, invalid double words, bound failures, and unresolved bound
tests have separate counts. No value is trimmed or replaced.

The main MPFR precision is 4,224 bits. A bound comparison at or near the bound
is repeated at 8,448 bits. A disagreement is reported as unresolved and is
counted as not established within the bound.

## RQ2 analysis

RQ2 includes all nine operations.

For a composite operation, the default rejected population contains
`weak_input_check` and `post_check`. The strong rejected population contains
`weak_input_check` and `strong_check`. They are analyzed separately and as a
union. Each wrapper row also records how the other wrapper acted on the same
cases.

For each rejected case, the QD result is classified as nonfinite, an invalid
double word, above the proved bound, within the proved bound, or unresolved.

For an error free transformation, the rejected population contains
`input_check`. A finite valid QD result is classified by exact reconstruction.

Unexpected outcomes are counted rather than treated as rejections.

## RQ3 analysis

RQ3 reads every recorded trial. No trial is removed.

For each timing series it reports the median, first quartile, third quartile,
and interquartile range. A ratio or time difference is formed for each pair
with the same trial number before the summary is computed. CompCert and Clang
are not paired with each other.

The timing reader checks the recorded timer, order schedule, trial count,
input count, and input fingerprint before it forms comparisons.

If compiler flags, compiler commands, or `QD_PREFIX` change, run `make clean`
before rebuilding.

## Direct analyzer use

The analyzer can also be invoked directly:

```sh
./analyze_rq1 results/numerical.tsv results/analysis/rq1.tsv
./analyze_rq2 results/numerical.tsv results/analysis/rq2.tsv
./analyze_rq3 results/timing-compcert.tsv results/timing-clang.tsv \
  results/analysis/rq3.tsv
```

It rejects any output path that names an input file.
