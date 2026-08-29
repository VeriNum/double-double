# dd_lib and QD comparison

`bench_all.cpp` runs the nine dd_lib arithmetic operations and the corresponding
QD operations on the same inputs. It reports output differences and median time
per call.

The dd_lib C files are compiled with CompCert. A C++ compiler builds the shared
test driver because QD is a C++ library. MPFR is used only to compare the values
represented by the returned component pairs.

## Requirements

- CompCert (`ccomp`)
- A C++14 compiler
- QD built with FMA support
- MPFR and GMP
- `pkg-config`, unless MPFR and GMP flags are supplied explicitly

`QD_PREFIX` is `/usr/local` by default. Set it when QD is installed elsewhere.

## Build and run

```sh
make QD_PREFIX=$HOME/.local/qd-fma
./bench_all [input_count] [trial_count]
```

The defaults are `2^22` inputs and 11 timing trials.

`bench_all` calls the checked public interface. To measure the unchecked
arithmetic kernels instead, run:

```sh
./bench_all_kernel [input_count] [trial_count]
```

Remove generated executables and object files with:

```sh
make clean
```

If a shared QD installation is outside the system search path, set
`LD_LIBRARY_PATH` on Linux or `DYLD_LIBRARY_PATH` on macOS when running the
benchmark.

## Inputs

Both libraries receive identical binary64 components.

- Every double-word input has a finite, nonzero high component.
- Four-fifths have a finite, nonzero low component smaller than one-quarter ulp
  of the high component.
- One-fifth have a zero low component, retaining ordinary-double cases.
- Every pair is checked with `hi + lo == hi` before use.
- High components and scalar divisors are resampled when zero. Division uses the
  same input distribution as the other operations.
- Fast2Sum inputs alone are reordered to satisfy `|a| >= |b|`.

The random inputs are drawn from `[-1,1]`. This program does not test exponent
extremes or boundary cases.

## Compared operations

| dd_lib | QD |
|---|---|
| `two_sum_guarded` | `qd::two_sum` |
| `fast_2sum_guarded` | `qd::quick_two_sum` |
| `fast_2mult_guarded` | `qd::two_prod` |
| `dw_plus_fp` | `dd_real + double` |
| `dw_times_fp` | `dd_real * double` |
| `dw_div_fp` | `dd_real / double` |
| `dw_plus_dw` | `dd_real::ieee_add` |
| `dw_times_dw` | `dd_real * dd_real` |
| `dw_div_dw` | `dd_real::accurate_div` |

The kernel build replaces the dd_lib functions above with their unchecked
counterparts. QD's accurate addition and division routines are selected
explicitly where QD offers more than one implementation.

## Output

For each operation, the differential pass reports:

- different high-component encodings;
- different low-component encodings;
- different represented values; and
- the largest relative gap, using the QD value as the denominator.

MPFR reconstructs each returned value as the exact sum `hi + lo`. Thus the
represented-value count does not lose differences through binary64 cancellation
or underflow.

QD is a comparison implementation, not an exact arithmetic oracle. A nonzero
gap shows that the libraries returned different values; it does not determine
which value is more accurate.

Timing results include one untimed warm-up pass and report the median nanoseconds
per call. The values in `RESULTS.md` are smoke-test results, not controlled
publication measurements.
