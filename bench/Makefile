# Benchmark harness: dd_lib (ours) vs QD (Bailey et al.)
#
# Variables you can override on the command line:
#   DD_CC       compiler for dd_lib .c files            (default: ccomp)
#   CXX         compiler for harness + linking          (default: g++)
#   DD_CFLAGS   flags for dd_lib .c files               (default: -O3)
#   CXXFLAGS    flags for harness                       (default: -O3 -fno-fast-math -std=c++14)
#   QD_PREFIX   install prefix where qd/ headers + libqd live   (default: /usr/local)
#
# CompCert builds the dd_lib objects. QD and the shared harness require C++ and
# therefore build with $(CXX).
#
# STRICT FLOAT: -fno-fast-math is NOT enough. clang/gcc default to FP contraction
# (-ffp-contract=on/fast), which fuses `a*b + c` into a single FMA and drops the
# intermediate rounding. That silently breaks the error-free transformations these
# double-word algorithms (and their Coq proofs) rely on: each `*` and `+` must be a
# separately-rounded IEEE op, and an FMA appears ONLY where the source calls fma().
# So we force -ffp-contract=off on both sides; explicit fma() calls remain FMA.
# Use an FMA-enabled QD build for two_prod parity. CompCert never contracts
# floating-point expressions, so the default dd_lib flags need no contraction
# option. Native compilers must be given strict floating-point flags explicitly.

DD_CC      ?= ccomp
CXX        ?= g++
DD_CFLAGS  ?= -O3
CXXFLAGS   ?= -O3 -fno-fast-math -ffp-contract=off -std=c++14 -Wall
QD_PREFIX  ?= /usr/local
PKG_CONFIG ?= pkg-config

MPFR_CFLAGS ?= $(shell $(PKG_CONFIG) --cflags mpfr gmp 2>/dev/null)
MPFR_LIBS   ?= $(shell $(PKG_CONFIG) --libs mpfr gmp 2>/dev/null)
ifeq ($(strip $(MPFR_LIBS)),)
MPFR_LIBS := -lmpfr -lgmp
endif

DD_LIB_DIR := ../dd_lib
DD_INC     := -I$(DD_LIB_DIR)/include
QD_INC     := -I$(QD_PREFIX)/include
QD_LIB     := -L$(QD_PREFIX)/lib -lqd

BENCHES    := bench_all bench_all_kernel
ALL_BINS   := $(BENCHES) probe_dw_div_dw_139
LEGACY_BINS := bench_all_default

# Arithmetic-only kernel baseline.  Keep wrapper and kernel objects distinct:
# the public dw_*.c files do not define their corresponding *_kernel symbols.
EFT_SRCS     := two_sum fast_2sum fast_2mult
DW_OPS       := dw_plus_fp dw_plus_dw dw_times_fp dw_times_dw dw_div_fp dw_div_dw
KERNEL_SRCS  := $(EFT_SRCS) $(addsuffix _kernel,$(DW_OPS))
KERNEL_OBJS  := $(addsuffix .o,$(KERNEL_SRCS))

# Exported default interface: guarded EFTs, and the default DW wrappers
# (weak input check, kernel, output-finiteness check).  Strong wrappers are not
# part of the evaluation even though they share the same source files.
DEFAULT_SRCS := $(KERNEL_SRCS) two_sum_guarded fast_2sum_guarded \
                fast_2mult_guarded fp_utils $(DW_OPS)
DEFAULT_OBJS := $(addsuffix .o,$(DEFAULT_SRCS))

all: $(BENCHES)

# --- dd_lib objects: generic rule (one .o per dd_lib .c) ------------------
%.o: $(DD_LIB_DIR)/%.c $(DD_LIB_DIR)/include/dw_arith.h
	$(DD_CC) $(DD_CFLAGS) $(DD_INC) -c $< -o $@

$(addsuffix .o,two_sum_guarded fast_2sum_guarded fast_2mult_guarded fp_utils $(DW_OPS)): \
  $(DD_LIB_DIR)/include/fp_utils.h

# --- harness objects ------------------------------------------------------
bench_all.o: bench_all.cpp
	$(CXX) $(CXXFLAGS) $(DD_INC) $(QD_INC) $(MPFR_CFLAGS) -c $< -o $@

bench_all_kernel.o: bench_all.cpp
	$(CXX) $(CXXFLAGS) -DUSE_KERNEL $(DD_INC) $(QD_INC) $(MPFR_CFLAGS) -c $< -o $@

# --- link -----------------------------------------------------------------
# Default public interface; use an FMA QD build for a fair mul/div comparison:
#   make QD_PREFIX=$(HOME)/.local/qd-fma bench_all
bench_all: bench_all.o $(DEFAULT_OBJS)
	$(CXX) $(CXXFLAGS) -o $@ $^ $(QD_LIB) $(MPFR_LIBS) -lm

# Unchecked arithmetic-kernel baseline.
#   make QD_PREFIX=$(HOME)/.local/qd-fma bench_all_kernel
bench_all_kernel: bench_all_kernel.o $(KERNEL_OBJS)
	$(CXX) $(CXXFLAGS) -o $@ $^ $(QD_LIB) $(MPFR_LIBS) -lm

# MPFR division-bound probe, linked against the current compiled kernels.
probe_dw_div_dw_139.o: probe_dw_div_dw_139.c
	$(DD_CC) $(DD_CFLAGS) $(DD_INC) $(MPFR_CFLAGS) -c $< -o $@

probe_dw_div_dw_139: probe_dw_div_dw_139.o $(KERNEL_OBJS)
	$(DD_CC) $(DD_CFLAGS) -o $@ $^ $(MPFR_LIBS) -lm

# --- convenience ----------------------------------------------------------
.PHONY: all clean run run-kernel
clean:
	rm -f *.o $(ALL_BINS) $(LEGACY_BINS)

run: bench_all
	./bench_all

run-kernel: bench_all_kernel
	./bench_all_kernel
