#ifndef BENCH_QD_EVALUATION_HPP
#define BENCH_QD_EVALUATION_HPP

#include <cmath>

// The evaluated QD operations are defined in QD's headers. Fix their
// configuration here so every run uses the inline FMA implementation.
#ifdef QD_INLINE
#undef QD_INLINE
#endif
#define QD_INLINE 1

#ifdef QD_FMA
#undef QD_FMA
#endif
#define QD_FMA(x, y, z) std::fma((x), (y), (z))

#ifdef QD_FMS
#undef QD_FMS
#endif
#define QD_FMS(x, y, z) std::fma((x), (y), -(z))

#include <qd/dd_real.h>

#endif
