# Evaluation harness

The evaluation has one driver for each research question:

- `rq1_accuracy.cpp` measures the bounds for the six double-word operations.
- `rq2_guard_acceptance.cpp` evaluates QD on inputs rejected by the checked
  double-word and error-free-transformation interfaces.
- `rq3_performance.cpp` times the guarded interfaces, unchecked kernels, and
  QD. It is built once with CompCert library objects and once with Clang
  library objects.

Input generation, MPFR measurements, boundary cases, and timing support are
kept in separate source files.

## Requirements

The harness requires CompCert, Clang, a GCC- or Clang-compatible C++14
compiler, MPFR, GMP, QD headers, and Python 3. It supports macOS
and Linux. CompCert and Clang build separate copies of the unchanged library
C files; the C++ compiler builds the drivers.

The build obtains MPFR and GMP flags from `pkg-config`. Set `MPFR_CFLAGS` and
`MPFR_LIBS` explicitly if they are not available there.

The repository layout keeps `dd_lib` next to this directory. An artifact may
instead place `dd_lib` inside this directory; the build detects both layouts.
Set `DD_LIB_DIR` only for a different source layout.

## Build and test

From this directory, run:

```sh
make prepare-evaluation
```

The build looks first for QD headers at `third_party/qd`, then uses
`qd-config` from `PATH`, and finally checks conventional system prefixes.
There are no user-specific paths. To make the submitted artifact
self-contained, its setup step should install the pinned QD headers under
`third_party/qd`; discovery itself does not download dependencies.

To select a particular installation, use either:

```sh
make QD_PREFIX=/absolute/path/to/qd prepare-evaluation
make QD_CONFIG=/absolute/path/to/qd-config prepare-evaluation
```

An explicit setting is checked as given and is never replaced by another
installation. Without a bundled or installed QD, `make` reports the missing
dependency and stops.

This builds the RQ1 and RQ2 drivers and both RQ3 binaries, then runs the C++
tests, the asserted RQ2 boundary suite, and the Python pipeline tests. The
build records the compiler,
flags, and QD files in `.build/config.json`; the runner refuses to use binaries
built with different settings. A routine `make clean` is unnecessary and does
not remove evaluation runs.

## Generate results

A smoke run checks the complete pipeline with 4,096 RQ3 timing cases and
without enforcing the frozen artifact build settings:

```sh
make smoke
```

To run the full artifact evaluation and generate its report:

```sh
make results
```

Both commands build the drivers and run all tests before executing the
evaluation. `make results` uses the frozen artifact workload and compiler
flags, but it does not require Git. The artifact timing workload uses 65,536
test cases and 24 trials per table cell. It prints the path to the generated
`RESULTS.md`. Make assigns a timestamped run identifier unless `RUN_ID` is
provided. Run directories are immutable, including failed runs.

Each run is stored under `runs/RUN_ID`:

```text
manifest.json
checksums.sha256
raw/
generated/
```

The manifest records the profile, available Git metadata, toolchain, binaries,
commands, input parameters, TSV metadata, and artifact hashes. Raw driver
output is kept separate from derived reports.

## Evaluation scope

| Question | Library interfaces | Reference or comparison |
|---|---|---|
| RQ1 bound tightness | default, six double-word operations | MPFR oracle; QD as a secondary comparison |
| RQ2 wrapper usefulness | checked interfaces for all nine operations; strong interface for double-word operations | QD on rejected test cases |
| RQ3 performance | default and kernel for all nine operations; strong interface for double-word operations | QD and Clang compiler ablation |

The default double-word interface uses the two-stage guard. The `dw_*_strong`
interface checks the stronger input-only conditions. Both call the same
unchecked kernel. Exact transformations have one guarded public interface.

RQ1 and RQ2 invoke the public C functions. Each RQ3 binary invokes the default
public function and kernel directly. For double-word operations it also invokes
the strong public function. Before timing, both guarded results must match the
kernel bit for bit.

## Inputs and measurements

The RQ1 and RQ2 numerical test inputs are deterministic and are created before
any guard runs. Binary64 values cover magnitude exponents -1074 through 1023.
Double-word sources cover exponents -969 through 1022. MPFR constructs odd
106-bit values; rounding the value and its exact residual produces the high
and low words. Five percent of double-word inputs retain an ordinary binary64
value with a zero low word. Signs are balanced in every exponent bin, and
operand streams are shuffled independently. RQ1 and RQ2 use the same generated
arrays and record the same numerical-input fingerprint.

RQ1 reconstructs inputs and results in MPFR. It reports the relative error
where the relative term of the bound dominates and the absolute error where
the absolute term dominates. Each range is reported as a percentage of the
operation's normally returned test cases. Bound fractions are computed per
case before their maximum and mean are taken. QD is measured on the same test
cases. Its error
relative to the `dd_lib` bound is contextual information, not a bound for QD;
QD may use a different algorithm. MPFR uses 2112-bit precision, with 4224 bits
for division cases. The report also gives the input-check, conditional
output-finiteness-check, and overall normal-return rates. Per-operation raw
counts are retained in `summary.json`. Every result above the bound is listed
with its case ID, inputs, result bits, reference, error, and bound.

RQ2 evaluates QD once for every generated test case rejected by an applicable
checked interface. Double-word operations are classified by finiteness,
double-word validity, and whether the QD error is within the `dd_lib` bound.
The default- and strong-interface results are reported in separate tables.
Each above-bound QD result is listed once, including every interface that
rejected its input.
Error-free transformations are classified by finiteness, double-word
validity, and exact reconstruction. The default- and strong-rejected
double-word populations overlap. The 48 named boundary cases are checked
separately and are excluded from reported percentages.

All QD drivers include `qd_evaluation.hpp`, which selects QD's inline
algorithms and maps `QD_FMA` and `QD_FMS` to C++ `std::fma`. This fixes the QD
arithmetic configuration independently of how a system QD library was built.

RQ3 compiles the same C sources once with CompCert and once with Clang using
`-fno-fast-math -ffp-contract=off`. The two compiler builds run as independent
timing blocks. Within each block, all measurement orders are balanced and
wrapper-to-kernel and wrapper-to-QD ratios use paired trials. The C compiler
label applies to the `dd_lib` objects; the harness and QD code use `CXX`.
Cross-compiler results are not treated as paired measurements. RQ3 uses a
separate timing-input set over exponents -100 through 100. Every timed series
for an operation uses the same cases, and the CompCert and Clang blocks record
the same timing-input fingerprint. Each timing observation is one complete
input sweep normalized to ns/call.

## Manual debugging

From `bench`, the drivers can be run directly while debugging:

```sh
cd bench
./rq1_accuracy [samples_per_exponent] [summary.tsv]
./rq2_guard_acceptance [samples_per_exponent] [cases.tsv]
./rq2_guard_acceptance --boundary-only [cases.tsv]
./rq3_performance_compcert [input_count] [trial_count] [trials.tsv]
./rq3_performance_clang [input_count] [trial_count] [trials.tsv]
```

Direct runs do not create a manifest or a generated report.

## Multiplication-underflow example

The standalone example contrasts the mixed `dw_times_dw` contract with the
exact-reconstruction `fast_2mult_guarded` contract for
`a = (1 + 2^-52) 2^-515`:

```sh
make multiplication_underflow_example
./multiplication_underflow_example
```
