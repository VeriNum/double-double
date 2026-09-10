# Benchmark harness: dd_lib (ours) vs QD (Bailey et al.)
#
# Variables you can override on the command line:
#   DD_CC       compiler for dd_lib .c files            (default: ccomp)
#   CLANG_CC    Clang compiler for comparison objects    (default: clang)
#   CXX         compiler for harness + linking          (default: g++)
#   DD_CFLAGS   flags for dd_lib .c files               (default: -O3)
#   CLANG_CFLAGS flags for Clang dd_lib objects          (default: -O3 -std=c11)
#   CXXFLAGS    non-floating-point C++ flags            (default: -O3 -std=c++14 -Wall)
#   DD_LIB_DIR  dd_lib source directory                  (default: local or ../dd_lib)
#   QD_PREFIX   install prefix containing the qd/ headers       (required)
#
# CompCert and Clang build separate copies of the unchanged dd_lib sources.
# QD and the shared harness require C++ and therefore build with $(CXX).
#
# STRICT FLOAT: -fno-fast-math is NOT enough. clang/gcc default to FP contraction
# (-ffp-contract=on/fast), which fuses `a*b + c` into a single FMA and drops the
# intermediate rounding. That silently breaks the error-free transformations these
# double-word algorithms (and their Coq proofs) rely on: each `*` and `+` must be a
# separately-rounded IEEE op, and an FMA appears ONLY where the source calls fma().
# So we force -ffp-contract=off on both sides; explicit fma() calls remain FMA.
# qd_evaluation.hpp selects QD's inline FMA implementation. CompCert never
# contracts floating-point expressions, so the default dd_lib flags need no
# contraction option. Native compilers need the strict flags above.

.DEFAULT_GOAL := all-results

DD_CC      ?= ccomp
CLANG_CC   ?= clang
CXX        ?= g++
DD_CFLAGS  ?= -O3
CLANG_CFLAGS ?= -O3 -std=c11
CXXFLAGS   ?= -O3 -std=c++14 -Wall
STRICT_FP_FLAGS := -fno-fast-math -ffp-contract=off
PKG_CONFIG ?= pkg-config

ifeq ($(origin DD_LIB_DIR), undefined)
  ifneq ($(wildcard dd_lib/include/dw_arith.h),)
    DD_LIB_DIR := dd_lib
  else
    DD_LIB_DIR := ../dd_lib
  endif
endif

MPFR_CFLAGS ?= $(shell $(PKG_CONFIG) --cflags mpfr gmp 2>/dev/null)
MPFR_LIBS   ?= $(shell $(PKG_CONFIG) --libs mpfr gmp 2>/dev/null)
ifeq ($(strip $(MPFR_LIBS)),)
MPFR_LIBS := -lmpfr -lgmp
endif

DD_INC     := -I$(DD_LIB_DIR)/include
QD_INC     := -I$(QD_PREFIX)/include

BUILD_DIR    := .build
CLANG_BUILD_DIR := $(BUILD_DIR)/clang

RUN_DIR ?= results
RUN_PATH := $(patsubst %/,%,$(RUN_DIR))
ANALYSIS_DIR ?= $(RUN_PATH)/analysis

SAMPLES_PER_EXPONENT ?= 40
NUM_INPUTS_FOR_PERF ?= 65536
NUM_TRIALS_FOR_PERF ?= 24

ANALYZERS := analyze_rq1 analyze_rq2 analyze_rq3
ALL_BINS := generate_numerical_data $(ANALYZERS) \
            generate_performance_data_compcert \
            generate_performance_data_clang

# Arithmetic-only kernel baseline.  Keep wrapper and kernel objects distinct:
# the public dw_*.c files do not define their corresponding *_kernel symbols.
EFT_SRCS     := two_sum fast_2sum fast_2mult
DW_OPS       := dw_plus_fp dw_plus_dw dw_times_fp dw_times_dw dw_div_fp dw_div_dw
KERNEL_SRCS  := $(EFT_SRCS) $(addsuffix _kernel,$(DW_OPS))

# The six dw_*.c files define both the default (two-stage) and strong
# (input-only) interfaces. Fast2Sum and Fast2Mult have guarded entry points.
LIBRARY_SRCS := $(KERNEL_SRCS) fast_2sum_guarded \
                fast_2mult_guarded fp_utils $(DW_OPS)
LIBRARY_OBJS := $(addsuffix .o,$(LIBRARY_SRCS))
CLANG_LIBRARY_OBJS := $(addprefix $(CLANG_BUILD_DIR)/,\
                        $(addsuffix .o,$(LIBRARY_SRCS)))

EVAL_COMMON_OBJS := input_generation.o
NUMERICAL_DATA_OBJS := generate_numerical_data.o $(EVAL_COMMON_OBJS)
PERFORMANCE_COMPCERT_OBJS := \
    $(BUILD_DIR)/generate_performance_data_compcert.o $(EVAL_COMMON_OBJS)
PERFORMANCE_CLANG_OBJS := \
    $(BUILD_DIR)/generate_performance_data_clang.o $(EVAL_COMMON_OBJS)

.PHONY: all-results raw-results analyze-results clean check-dependencies

check-dependencies:
	@test -f "$(DD_LIB_DIR)/include/dw_arith.h" || { \
	  echo "dd_lib headers not found under $(DD_LIB_DIR)" >&2; \
	  echo "Set DD_LIB_DIR to the dd_lib source directory." >&2; \
	  exit 1; \
	}
	@test -n "$(QD_PREFIX)" || { \
	  echo "QD_PREFIX is required" >&2; \
	  exit 1; \
	}
	@test -f "$(QD_PREFIX)/include/qd/dd_real.h" || { \
	  echo "QD headers not found under $(QD_PREFIX)" >&2; \
	  echo "Set QD_PREFIX to the QD installation prefix." >&2; \
	  exit 1; \
	}

$(BUILD_DIR):
	mkdir -p $@

$(CLANG_BUILD_DIR): | $(BUILD_DIR)
	mkdir -p $@

# --- dd_lib objects: generic rule (one .o per dd_lib .c) ------------------
%.o: $(DD_LIB_DIR)/%.c $(DD_LIB_DIR)/include/dw_arith.h | check-dependencies
	$(DD_CC) $(DD_CFLAGS) $(DD_INC) -c $< -o $@

$(addsuffix .o,fast_2sum_guarded fast_2mult_guarded fp_utils $(DW_OPS)): \
  $(DD_LIB_DIR)/include/fp_utils.h

$(CLANG_BUILD_DIR)/%.o: $(DD_LIB_DIR)/%.c \
                        $(DD_LIB_DIR)/include/dw_arith.h \
                        | $(CLANG_BUILD_DIR) check-dependencies
	$(CLANG_CC) $(CLANG_CFLAGS) $(STRICT_FP_FLAGS) $(DD_INC) -c $< -o $@

$(addprefix $(CLANG_BUILD_DIR)/,\
  $(addsuffix .o,fast_2sum_guarded fast_2mult_guarded fp_utils $(DW_OPS))): \
  $(DD_LIB_DIR)/include/fp_utils.h

# --- C++ analysis objects -------------------------------------------------
analysis_support.o: analysis_support.cpp analysis_support.hpp
	$(CXX) $(CXXFLAGS) $(STRICT_FP_FLAGS) $(MPFR_CFLAGS) -MMD -MP -c $< -o $@

analyze_rq1.o: analyze_rq1.cpp analysis_support.hpp
	$(CXX) $(CXXFLAGS) $(STRICT_FP_FLAGS) -MMD -MP -c $< -o $@

analyze_rq2.o: analyze_rq2.cpp analysis_support.hpp
	$(CXX) $(CXXFLAGS) $(STRICT_FP_FLAGS) -MMD -MP -c $< -o $@

analyze_rq3.o: analyze_rq3.cpp analysis_support.hpp
	$(CXX) $(CXXFLAGS) $(STRICT_FP_FLAGS) -MMD -MP -c $< -o $@

# --- C++ generation objects -----------------------------------------------
%.o: %.cpp | check-dependencies
	$(CXX) $(CXXFLAGS) $(STRICT_FP_FLAGS) $(DD_INC) $(QD_INC) $(MPFR_CFLAGS) \
	  -I. -MMD -MP -c $< -o $@

$(BUILD_DIR)/generate_performance_data_compcert.o: \
        generate_performance_data.cpp | $(BUILD_DIR) check-dependencies
	$(CXX) $(CXXFLAGS) $(STRICT_FP_FLAGS) $(DD_INC) $(QD_INC) $(MPFR_CFLAGS) \
	  -I. -DDD_BUILD_LABEL=\"compcert\" -MMD -MP -c $< -o $@

$(BUILD_DIR)/generate_performance_data_clang.o: \
        generate_performance_data.cpp | $(BUILD_DIR) check-dependencies
	$(CXX) $(CXXFLAGS) $(STRICT_FP_FLAGS) $(DD_INC) $(QD_INC) $(MPFR_CFLAGS) \
	  -I. -DDD_BUILD_LABEL=\"clang\" -MMD -MP -c $< -o $@

# --- benchmark links ------------------------------------------------------
generate_numerical_data: $(NUMERICAL_DATA_OBJS) $(LIBRARY_OBJS)
	$(CXX) $(CXXFLAGS) $(STRICT_FP_FLAGS) -o $@ $^ $(MPFR_LIBS) -lm

analyze_rq1: analyze_rq1.o analysis_support.o
	$(CXX) $(CXXFLAGS) $(STRICT_FP_FLAGS) -o $@ $^ $(MPFR_LIBS)

analyze_rq2: analyze_rq2.o analysis_support.o
	$(CXX) $(CXXFLAGS) $(STRICT_FP_FLAGS) -o $@ $^ $(MPFR_LIBS)

analyze_rq3: analyze_rq3.o analysis_support.o
	$(CXX) $(CXXFLAGS) $(STRICT_FP_FLAGS) -o $@ $^ $(MPFR_LIBS)

generate_performance_data_compcert: $(PERFORMANCE_COMPCERT_OBJS) $(LIBRARY_OBJS)
	$(CXX) $(CXXFLAGS) $(STRICT_FP_FLAGS) -o $@ $^ $(MPFR_LIBS) -lm

generate_performance_data_clang: $(PERFORMANCE_CLANG_OBJS) $(CLANG_LIBRARY_OBJS)
	$(CXX) $(CXXFLAGS) $(STRICT_FP_FLAGS) -o $@ $^ $(MPFR_LIBS) -lm

# --- measurement and analysis workflow -----------------------------------
clean:
	rm -f *.o *.d $(ALL_BINS)
	rm -rf "$(BUILD_DIR)"

all-results:
	+$(MAKE) --no-print-directory raw-results RUN_DIR="$(RUN_PATH)"
	+$(MAKE) --no-print-directory analyze-results \
	  RUN_DIR="$(RUN_PATH)" ANALYSIS_DIR="$(ANALYSIS_DIR)"
	@echo "Analysis files: $(ANALYSIS_DIR)"

raw-results: generate_numerical_data generate_performance_data_compcert \
             generate_performance_data_clang
	@test -n "$(RUN_PATH)" || { echo "RUN_DIR is required" >&2; exit 1; }
	mkdir -p "$(RUN_PATH)"
	@test ! -e "$(RUN_PATH)/numerical.tsv" || { echo "$(RUN_PATH)/numerical.tsv already exists" >&2; exit 1; }
	@test ! -e "$(RUN_PATH)/timing-compcert.tsv" || { echo "$(RUN_PATH)/timing-compcert.tsv already exists" >&2; exit 1; }
	@test ! -e "$(RUN_PATH)/timing-clang.tsv" || { echo "$(RUN_PATH)/timing-clang.tsv already exists" >&2; exit 1; }
	@test ! -e "$(RUN_PATH)/numerical.tsv.partial" || { echo "$(RUN_PATH)/numerical.tsv.partial already exists" >&2; exit 1; }
	@test ! -e "$(RUN_PATH)/timing-compcert.tsv.partial" || { echo "$(RUN_PATH)/timing-compcert.tsv.partial already exists" >&2; exit 1; }
	@test ! -e "$(RUN_PATH)/timing-clang.tsv.partial" || { echo "$(RUN_PATH)/timing-clang.tsv.partial already exists" >&2; exit 1; }
	./generate_numerical_data "$(SAMPLES_PER_EXPONENT)" "$(RUN_PATH)/numerical.tsv.partial"
	./generate_performance_data_compcert "$(NUM_INPUTS_FOR_PERF)" "$(NUM_TRIALS_FOR_PERF)" "$(RUN_PATH)/timing-compcert.tsv.partial"
	./generate_performance_data_clang "$(NUM_INPUTS_FOR_PERF)" "$(NUM_TRIALS_FOR_PERF)" "$(RUN_PATH)/timing-clang.tsv.partial"
	mv "$(RUN_PATH)/numerical.tsv.partial" "$(RUN_PATH)/numerical.tsv"
	mv "$(RUN_PATH)/timing-compcert.tsv.partial" "$(RUN_PATH)/timing-compcert.tsv"
	mv "$(RUN_PATH)/timing-clang.tsv.partial" "$(RUN_PATH)/timing-clang.tsv"

analyze-results: $(ANALYZERS)
	@test -f "$(RUN_PATH)/numerical.tsv" || { echo "$(RUN_PATH)/numerical.tsv not found" >&2; exit 1; }
	@test -f "$(RUN_PATH)/timing-compcert.tsv" || { echo "$(RUN_PATH)/timing-compcert.tsv not found" >&2; exit 1; }
	@test -f "$(RUN_PATH)/timing-clang.tsv" || { echo "$(RUN_PATH)/timing-clang.tsv not found" >&2; exit 1; }
	mkdir -p "$(ANALYSIS_DIR)"
	./analyze_rq1 "$(RUN_PATH)/numerical.tsv" \
	  "$(ANALYSIS_DIR)/rq1.tsv.partial"
	./analyze_rq2 "$(RUN_PATH)/numerical.tsv" \
	  "$(ANALYSIS_DIR)/rq2.tsv.partial"
	./analyze_rq3 "$(RUN_PATH)/timing-compcert.tsv" \
	  "$(RUN_PATH)/timing-clang.tsv" \
	  "$(ANALYSIS_DIR)/rq3.tsv.partial"
	mv "$(ANALYSIS_DIR)/rq1.tsv.partial" "$(ANALYSIS_DIR)/rq1.tsv"
	mv "$(ANALYSIS_DIR)/rq2.tsv.partial" "$(ANALYSIS_DIR)/rq2.tsv"
	mv "$(ANALYSIS_DIR)/rq3.tsv.partial" "$(ANALYSIS_DIR)/rq3.tsv"
-include $(wildcard *.d $(BUILD_DIR)/*.d)
