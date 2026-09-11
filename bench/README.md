# Benchmark tools

The benchmark has one measurement path and one analysis path.

- `generate_numerical_data.cpp` records the numerical inputs, wrapper statuses,
  FenceDD results, and QD results.
- `generate_performance_data.cpp` records every timing trial. It is linked once with
  CompCert objects and once with Clang objects.
- `analyze_rq1.cpp`, `analyze_rq2.cpp`, and `analyze_rq3.cpp` analyze one
  research question each.
- `generate_paper_tables.py` formats the analysis TSV files as LaTeX table
  rows.
- `numerical_analysis.cpp` contains the numerical parser and MPFR work shared
  by RQ1 and RQ2.
- `analysis_common.hpp` contains the small schema and file helpers shared by
  all three analyzers.

The analyzers do not link FenceDD or QD. They cannot execute the measured
implementations. They read the raw files and write derived files elsewhere.

All objects, dependency files, and executables are written below `.build/`.
Source files remain at the top of this directory, and measured data remains
under the selected result directory.

## Requirements

The measurement programs require CompCert, Clang, a C++14 compiler, MPFR,
GMP, and QD headers. The RQ1 and RQ2 analyzers require a C++14 compiler,
MPFR, and GMP. The RQ3 analyzer requires only a C++14 compiler.

The build obtains MPFR and GMP flags from `pkg-config`. Set `MPFR_CFLAGS` and
`MPFR_LIBS` if they cannot be found that way.

`QD_PREFIX` is required when measurement programs are built. For example:

```sh
make QD_PREFIX=/absolute/path/to/qd all-results RUN_DIR=results/
```

`FENCEDD_DIR` may be used when `fenceDD` is not next to this directory.

## Full run

From this directory, run:

```sh
make QD_PREFIX=/absolute/path/to/qd all-results RUN_DIR=results/
```

This runs the full measurement first, the analysis second, and the LaTeX
formatting last. It produces:

```text
results/
  numerical.tsv
  timing-compcert.tsv
  timing-clang.tsv
  analysis/
    rq1.tsv
    rq2.tsv
    rq3.tsv
  tex/
    rq1-relative.tex
    rq1-absolute.tex
    rq2-composite.tex
    rq2-transformations.tex
    rq3-default.tex
    rq3-strong.tex
```

The `make raw-results` command refuses to overwrite existing data files. The
analysis files are derived and may be regenerated.

## Separate steps

The same work may be run in separate commands:

```sh
make QD_PREFIX=/absolute/path/to/qd raw-results RUN_DIR=results/
make analyze-results RUN_DIR=results/
make tex-results RUN_DIR=results/
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

The first line, `# samples_per_exponent=N`, records the number of values
generated for each exponent bin. The remaining columns are:

| Column | Meaning |
| --- | --- |
| `operation` | Operation that was called. |
| `case_id` | Zero based case number within that operation. Operations that share an input set use the same case number for the same inputs. |
| `first_hi_bits` | Exact binary64 bits of the first input, or its high part. |
| `first_lo_bits` | Exact bits of the first low part, or `-` when the first input is a single binary64 value. |
| `second_hi_bits` | Exact binary64 bits of the second input, or its high part. |
| `second_lo_bits` | Exact bits of the second low part, or `-` when the second input is a single binary64 value. |
| `default_status` | Integer returned by the default wrapper, or `-` when the operation has no status. |
| `default_result_hi_bits` | Exact bits of the default result high part, or `-` when the call rejected. |
| `default_result_lo_bits` | Exact bits of the default result low part, or `-` when the call rejected. |
| `strong_status` | Integer returned by the strong wrapper, or `-` when the operation has no strong wrapper. |
| `strong_result_hi_bits` | Exact bits of the strong result high part, or `-` when no strong result is available. |
| `strong_result_lo_bits` | Exact bits of the strong result low part, or `-` when no strong result is available. |
| `qd_result_hi_bits` | Exact bits of the QD result high part. |
| `qd_result_lo_bits` | Exact bits of the QD result low part. |

The status codes are:

| Code | Meaning |
| --- | --- |
| `0` | The call returned a result. |
| `1` | The weak input check rejected the input. |
| `2` | The post check rejected the computed result. |
| `3` | The strong input check rejected the input. |

All error free transformations record a default status. They record `-` for
the strong fields because they have no strong wrapper.

The default and strong calls are recorded independently. Generation does not
require their statuses or returned bits to match.

## Raw timing data

`timing-compcert.tsv` and `timing-clang.tsv` have the same format. The `build`
metadata value identifies which FenceDD objects were linked into that
measurement program. Every data row records one complete pass over the timing
inputs, divided by the number of calls in that pass.

The metadata lines before the header are:

| Name | Meaning |
| --- | --- |
| `rq3_schema_version` | Timing file schema expected by the RQ3 analyzer. |
| `build` | FenceDD build used by this file: `compcert` or `clang`. |
| `input_count` | Number of function inputs used in every trial. |
| `trial_count` | Number of trials recorded for every timing series. |
| `composite_interfaces` | Meaning of the default and strong composite interfaces. |
| `exact_transform_interface` | Meaning of the default error free transformation interface. |
| `quantile` | Quantile rule used when summaries are formed. |
| `exact_schedule` | Order balancing schedule for the three error free transformation variants. |
| `composite_schedule` | Order balancing schedule for the four composite variants. |
| `timer` | Clock used to measure elapsed time. |
| `input_fingerprint` | 64 bit fingerprint of the exact timing inputs. The two timing files must match. |

The two footer lines record `data_rows`, the number of timing rows, and
`completed=true`, which shows that generation reached the end of the run.

The timing columns are:

| Column | Meaning |
| --- | --- |
| `operation` | Operation that was timed. |
| `implementation` | `fenceDD` or `QD`. |
| `interface` | FenceDD `default`, `strong`, or `kernel`, or QD `reference`. |
| `trial` | Zero based trial number within the timing series. |
| `ns_per_call` | Elapsed nanoseconds for the full pass divided by `input_count`. |

## RQ1 analysis

RQ1 uses the six composite operations. A case is eligible when the default
wrapper returned status `0`.

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

Each row summarizes one operation, one implementation, and one regime. The
analyzer writes all three regimes for each implementation, including regimes
with no cases. The columns are:

| Column | Meaning |
| --- | --- |
| `operation` | Composite operation being analyzed. |
| `implementation` | Result being measured: the FenceDD default wrapper or QD. |
| `regime` | `relative`, `absolute`, or `zero_bound`. This is a property of the reference value and proved bound, so FenceDD and QD use the same case populations. |
| `precision_bits` | MPFR precision used for reference values, errors, and ordinary bound comparisons. |
| `check_precision_bits` | MPFR precision used to repeat close bound comparisons. |
| `eligible_cases` | Cases where the FenceDD default wrapper returned status `0`. This count is repeated for every implementation and regime row for the operation. |
| `regime_cases` | Eligible cases assigned to this row regime. |
| `finite_results` | Results whose high and low parts are both finite. |
| `nonfinite_results` | Results containing infinity or NaN. |
| `invalid_double_words` | Finite result pairs for which rounding high plus low to binary64 does not recover the high part. |
| `values_without_error` | Finite results for which the selected error measure could not be formed. |
| `error_measure` | `relative_error` in the relative regime and `absolute_error` otherwise. |
| `finite_error_count` | Number of error values included in the error statistics. |
| `finite_error_sum` | Sum of those error values. |
| `finite_error_mean` | Error sum divided by error count. |
| `finite_error_max` | Largest error value. |
| `finite_error_max_case_id` | Case number that produced the largest error. Use it with `operation` to find the raw row. |
| `finite_bound_ratio_count` | Number of cases for which actual absolute error divided by the full proved absolute bound could be formed. |
| `finite_bound_ratio_sum` | Sum of those bound ratios. |
| `finite_bound_ratio_mean` | Bound ratio sum divided by bound ratio count. |
| `finite_bound_ratio_max` | Largest bound ratio. A resolved ratio greater than one is above the bound. |
| `finite_bound_ratio_max_case_id` | Case number that produced the largest bound ratio. |
| `not_within_bound` | Sum of nonfinite results, finite results above the bound, and unresolved comparisons. |
| `finite_above_bound` | Finite results whose actual error is strictly greater than the proved bound. |
| `bound_checks` | Close comparisons that were repeated using `check_precision_bits`. This is not the count of all ordinary bound comparisons. |
| `unresolved_bounds` | Comparisons for which the ordinary and higher precision tests disagree about whether the error exceeds the bound. |

`-` means that a statistic has no values in that row.

## RQ2 analysis

RQ2 includes all nine operations.

For a composite operation, the default rejected population contains
status `1` and status `2`. The strong rejected population contains status `3`.
They are analyzed separately and as a union. Each wrapper row also records how
the other wrapper acted on the same cases.

For each rejected case, the QD result is classified as nonfinite, an invalid
double word, above the proved bound, within the proved bound, or unresolved.

For an error free transformation, the rejected population contains
status `1`. A finite valid QD result is classified by exact reconstruction.

Unexpected status codes are counted rather than treated as rejections.

Each default or strong row describes one wrapper path. Each `either` row
describes the union of cases rejected by either composite wrapper. The columns
are:

| Column | Meaning |
| --- | --- |
| `operation` | Operation being analyzed. |
| `wrapper` | `default`, `strong`, or `either`. Error free transformations have only a default row. |
| `criterion` | `exact_reconstruction` for error free transformations or `error_bound` for composite operations. |
| `precision_bits` | MPFR precision used for reference values and ordinary comparisons. |
| `check_precision_bits` | MPFR precision used to repeat close bound comparisons. |
| `total_cases` | All generated cases considered by this row. |
| `successful_cases` | Cases with status `0`. Not reported for an `either` row. |
| `status_0` | Cases where this wrapper returned status `0`. |
| `status_1` | Cases where this wrapper returned status `1`. |
| `status_2` | Cases where this wrapper returned status `2`. |
| `status_3` | Cases where this wrapper returned status `3`. |
| `other_status` | Cases where this wrapper returned an integer outside status codes 0 through 3. |
| `no_status` | Cases with no status value. This should be zero for current operations. |
| `rejected_cases` | Population whose QD results are classified in this row. This is status 1 for an error free transformation, status 1 or 2 for a default composite wrapper, status 3 for a strong wrapper, or their union for `either`. |
| `unexpected_statuses` | Cases that are neither successful nor a rejection expected for this row. |
| `other_wrapper_successful` | Among cases rejected by this wrapper, cases where the other wrapper succeeded. |
| `other_wrapper_rejected` | Among cases rejected by this wrapper, cases where the other wrapper also had its expected rejection. |
| `other_wrapper_unexpected_status` | Among cases rejected by this wrapper, cases where the other wrapper was neither successful nor had its expected rejection. |
| `qd_nonfinite` | Rejected cases whose QD result contains infinity or NaN. |
| `qd_invalid_double_word` | Rejected cases whose finite QD pair does not satisfy the double word representation test. |
| `qd_no_reference` | Rejected cases for which no usable reference error was available. |
| `qd_failed` | Rejected cases where QD is not exact for an error free transformation or exceeds the proved bound for a composite operation. |
| `qd_passed` | Rejected cases where QD is exact for an error free transformation or is at or below the proved bound for a composite operation. |
| `qd_bound_checks` | QD bound comparisons repeated using `check_precision_bits`. |
| `qd_unresolved_bounds` | QD comparisons for which the ordinary and higher precision tests disagree. |

Columns that do not apply to an `either` row or an error free transformation
contain `-`. The six QD classification columns partition `rejected_cases`.

## RQ3 analysis

RQ3 reads every recorded trial. No trial is removed.

For each timing series it reports the median, first quartile, third quartile,
and interquartile range. A ratio or time difference is formed for each pair
with the same trial number before the summary is computed. CompCert and Clang
are not paired with each other.

The timing reader checks the recorded timer, order schedule, trial count,
input count, and input fingerprint before it forms comparisons.

The `measure` column uses the following names:

| Measure | Value summarized across trials |
| --- | --- |
| `default_ns_per_call` | FenceDD default wrapper time per call. |
| `strong_ns_per_call` | FenceDD strong wrapper time per call. Composite operations only. |
| `kernel_ns_per_call` | FenceDD unchecked kernel time per call. |
| `qd_ns_per_call` | QD time per call. |
| `default_over_kernel` | Default time divided by kernel time for the same trial. |
| `default_minus_kernel_ns` | Default time minus kernel time for the same trial, in nanoseconds per call. |
| `default_over_qd` | Default time divided by QD time for the same trial. |
| `strong_over_kernel` | Strong time divided by kernel time for the same trial. Composite operations only. |
| `strong_minus_kernel_ns` | Strong time minus kernel time for the same trial, in nanoseconds per call. Composite operations only. |
| `strong_over_qd` | Strong time divided by QD time for the same trial. Composite operations only. |

The RQ3 columns are:

| Column | Meaning |
| --- | --- |
| `build` | FenceDD build measured in the source timing file: `compcert` or `clang`. |
| `operation` | Operation being summarized. |
| `measure` | Timing series, paired ratio, or paired difference listed above. |
| `input_count` | Number of function calls in each timed pass. |
| `sample_count` | Number of trial values summarized. |
| `median` | Median of the trial values. |
| `first_quartile` | 25th percentile using linear interpolation at position `p * (n - 1)`. |
| `third_quartile` | 75th percentile using the same rule. |
| `iqr` | Third quartile minus first quartile. |

Time rows and time differences are in nanoseconds per call. Ratio rows have no
unit.

## LaTeX table files

`make tex-results RUN_DIR=results/` reads the three analysis TSV files and
writes table rows below `results/tex/`. `TEX_DIR` may be set to use another
output directory.

The Python formatter uses fixed operation, implementation, wrapper, regime,
build, and measure selections. It takes timing ratios, differences, medians,
and interquartile ranges directly from `rq3.tsv`. It forms display percentages
directly from the counts in `rq1.tsv` and `rq2.tsv`, applies the declared
display rounding, and writes LaTeX syntax. It does not read raw measurement
files or change analysis files.

The generated files contain table rows rather than complete table
environments:

| File | Contents |
| --- | --- |
| `rq1-relative.tex` | Relative regime rows for the six composite operations. |
| `rq1-absolute.tex` | Absolute regime rows for the four operations with mixed bounds. |
| `rq2-composite.tex` | Default and strong rejection rows for the six composite operations. |
| `rq2-transformations.tex` | Rejection rows for the three error free transformations. |
| `rq3-default.tex` | Default wrapper performance rows for Table 5. |
| `rq3-strong.tex` | Strong wrapper performance rows for Table 6. |

RQ1 bound ratios use four digits after the decimal point. RQ1 and RQ2
percentages use two digits after the decimal point. RQ3 medians and
interquartile ranges use two significant digits. Ties use round to nearest
with ties to even.

If compiler flags, compiler commands, or `QD_PREFIX` change, run `make clean`
before rebuilding.

## Direct analyzer use

The analyzer can also be invoked directly:

```sh
.build/bin/analyze_rq1 results/numerical.tsv results/analysis/rq1.tsv
.build/bin/analyze_rq2 results/numerical.tsv results/analysis/rq2.tsv
.build/bin/analyze_rq3 results/timing-compcert.tsv results/timing-clang.tsv \
  results/analysis/rq3.tsv
python3 generate_paper_tables.py results/analysis results/tex
```

It rejects any output path that names an input file.
