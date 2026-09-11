# Benchmark harness: fenceDD vs QD (Bailey et al.)
#
# Variables you can override on the command line:
#   FENCEDD_CC  compiler for fenceDD .c files            (default: ccomp)
#   CLANG_CC    Clang C compiler for comparison objects  (default: clang)
#   CLANG_CXX   matching Clang C++ compiler              (default: beside CLANG_CC)
#   FENCEDD_CFLAGS flags for fenceDD .c files             (default: -O3)
#   CLANG_CFLAGS flags for Clang fenceDD objects          (default: -O3 -std=c11)
#   CXXFLAGS    non-floating-point C++ flags            (default: -O3 -std=c++14 -Wall)
#   FENCEDD_DIR fenceDD source directory                  (default: local or ../fenceDD)
#   QD_PREFIX   install prefix containing the qd/ headers       (required)
#
# CompCert and Clang build separate copies of the unchanged fenceDD sources.
# QD and the shared harness require C++ and therefore build with
# $(CLANG_CXX). The dependency check requires the C and C++ compilers to
# report the same Clang distribution and version.
#
# STRICT FLOAT: -fno-fast-math is NOT enough. clang/gcc default to FP contraction
# (-ffp-contract=on/fast), which fuses `a*b + c` into a single FMA and drops the
# intermediate rounding. That silently breaks the error-free transformations these
# double-word algorithms (and their Coq proofs) rely on: each `*` and `+` must be a
# separately-rounded IEEE op, and an FMA appears ONLY where the source calls fma().
# So we force -ffp-contract=off on both sides; explicit fma() calls remain FMA.
# qd_evaluation.hpp selects QD's inline FMA implementation. CompCert never
# contracts floating-point expressions, so the default fenceDD flags need no
# contraction option. Native compilers need the strict flags above.

.DEFAULT_GOAL := all-results

FENCEDD_CC ?= ccomp
CLANG_CC   ?= clang
CLANG_CC_PATH := $(shell command -v $(CLANG_CC) 2>/dev/null)
CLANG_CXX  ?= $(if $(CLANG_CC_PATH),$(dir $(CLANG_CC_PATH))clang++,clang++)
FENCEDD_CFLAGS ?= -O3
CLANG_CFLAGS ?= -O3 -std=c11
CXXFLAGS   ?= -O3 -std=c++14 -Wall
STRICT_FP_FLAGS := -fno-fast-math -ffp-contract=off
PKG_CONFIG ?= pkg-config
PYTHON     ?= python3

ifeq ($(origin FENCEDD_DIR), undefined)
  ifneq ($(wildcard fenceDD/include/dw_arith.h),)
    FENCEDD_DIR := fenceDD
  else
    FENCEDD_DIR := ../fenceDD
  endif
endif

MPFR_CFLAGS ?= $(shell $(PKG_CONFIG) --cflags mpfr gmp 2>/dev/null)
MPFR_LIBS   ?= $(shell $(PKG_CONFIG) --libs mpfr gmp 2>/dev/null)
ifeq ($(strip $(MPFR_LIBS)),)
MPFR_LIBS := -lmpfr -lgmp
endif

FENCEDD_INC := -I$(FENCEDD_DIR)/include
QD_INC     := -I$(QD_PREFIX)/include

BUILD_DIR := .build
BIN_DIR := $(BUILD_DIR)/bin
CXX_OBJ_DIR := $(BUILD_DIR)/obj/cxx
COMPCERT_OBJ_DIR := $(BUILD_DIR)/obj/compcert
CLANG_OBJ_DIR := $(BUILD_DIR)/obj/clang

RUN_DIR ?= results
RUN_PATH := $(patsubst %/,%,$(RUN_DIR))
ANALYSIS_DIR ?= $(RUN_PATH)/analysis
TEX_DIR ?= $(RUN_PATH)/tex

SAMPLES_PER_EXPONENT ?= 40
NUM_INPUTS_FOR_PERF ?= 65536
NUM_TRIALS_FOR_PERF ?= 24

ANALYZERS := $(BIN_DIR)/analyze_rq1 $(BIN_DIR)/analyze_rq2 \
             $(BIN_DIR)/analyze_rq3

# Arithmetic-only kernel baseline.  Keep wrapper and kernel objects distinct:
# the public dw_*.c files do not define their corresponding *_kernel symbols.
EFT_SRCS     := two_sum_kernel fast_2sum_kernel fast_2mult_kernel
DW_OPS       := dw_plus_fp dw_plus_dw dw_times_fp dw_times_dw dw_div_fp dw_div_dw
KERNEL_SRCS  := $(EFT_SRCS) $(addsuffix _kernel,$(DW_OPS))

# The six dw_*.c files define both the default (two-stage) and strong
# (input-only) interfaces. Fast2Sum and Fast2Mult have public wrappers.
LIBRARY_SRCS := $(KERNEL_SRCS) two_sum fast_2sum fast_2mult fp_utils $(DW_OPS)
COMPCERT_LIBRARY_OBJS := $(addprefix $(COMPCERT_OBJ_DIR)/,\
                           $(addsuffix .o,$(LIBRARY_SRCS)))
CLANG_LIBRARY_OBJS := $(addprefix $(CLANG_OBJ_DIR)/,\
                        $(addsuffix .o,$(LIBRARY_SRCS)))

INPUT_GENERATION_OBJ := $(CXX_OBJ_DIR)/input_generation.o
NUMERICAL_DATA_OBJS := $(CXX_OBJ_DIR)/generate_numerical_data.o \
                       $(INPUT_GENERATION_OBJ)
PERFORMANCE_COMPCERT_OBJS := \
    $(CXX_OBJ_DIR)/generate_performance_data_compcert.o \
    $(INPUT_GENERATION_OBJ)
PERFORMANCE_CLANG_OBJS := \
    $(CXX_OBJ_DIR)/generate_performance_data_clang.o \
    $(INPUT_GENERATION_OBJ)

.PHONY: all-results raw-results analyze-results tex-results clean \
        check-dependencies

check-dependencies:
	@test -n "$(CLANG_CC_PATH)" || { \
	  echo "Clang C compiler not found: $(CLANG_CC)" >&2; \
	  exit 1; \
	}
	@command -v "$(CLANG_CXX)" >/dev/null 2>&1 || { \
	  echo "Clang C++ compiler not found: $(CLANG_CXX)" >&2; \
	  exit 1; \
	}
	@c_version="$$( $(CLANG_CC) --version | sed -n '1p' )"; \
	 cxx_version="$$( $(CLANG_CXX) --version | sed -n '1p' )"; \
	 test "$$c_version" = "$$cxx_version" || { \
	   echo "CLANG_CC and CLANG_CXX must use the same Clang distribution and version." >&2; \
	   echo "CLANG_CC:  $$c_version" >&2; \
	   echo "CLANG_CXX: $$cxx_version" >&2; \
	   exit 1; \
	 }
	@test -f "$(FENCEDD_DIR)/include/dw_arith.h" || { \
	  echo "fenceDD headers not found under $(FENCEDD_DIR)" >&2; \
	  echo "Set FENCEDD_DIR to the fenceDD source directory." >&2; \
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

$(BIN_DIR) $(CXX_OBJ_DIR) $(COMPCERT_OBJ_DIR) $(CLANG_OBJ_DIR):
	mkdir -p "$@"

# --- fenceDD objects: generic rule (one .o per fenceDD .c) ----------------
$(COMPCERT_OBJ_DIR)/%.o: $(FENCEDD_DIR)/%.c \
                         $(FENCEDD_DIR)/include/dw_arith.h \
                         | $(COMPCERT_OBJ_DIR) check-dependencies
	$(FENCEDD_CC) $(FENCEDD_CFLAGS) $(FENCEDD_INC) -c $< -o $@

$(addprefix $(COMPCERT_OBJ_DIR)/,\
  $(addsuffix .o,two_sum fast_2sum fast_2mult fp_utils $(DW_OPS))): \
    $(FENCEDD_DIR)/include/fp_utils.h

$(CLANG_OBJ_DIR)/%.o: $(FENCEDD_DIR)/%.c \
                      $(FENCEDD_DIR)/include/dw_arith.h \
                      | $(CLANG_OBJ_DIR) check-dependencies
	$(CLANG_CC) $(CLANG_CFLAGS) $(STRICT_FP_FLAGS) $(FENCEDD_INC) -c $< -o $@

$(addprefix $(CLANG_OBJ_DIR)/,\
  $(addsuffix .o,two_sum fast_2sum fast_2mult fp_utils $(DW_OPS))): \
    $(FENCEDD_DIR)/include/fp_utils.h

# --- C++ analysis objects -------------------------------------------------
$(CXX_OBJ_DIR)/numerical_analysis.o: numerical_analysis.cpp \
        numerical_analysis.hpp analysis_common.hpp | $(CXX_OBJ_DIR)
	$(CLANG_CXX) $(CXXFLAGS) $(STRICT_FP_FLAGS) $(MPFR_CFLAGS) -MMD -MP -c $< -o $@

$(CXX_OBJ_DIR)/analyze_rq1.o: analyze_rq1.cpp numerical_analysis.hpp \
        analysis_common.hpp | $(CXX_OBJ_DIR)
	$(CLANG_CXX) $(CXXFLAGS) $(STRICT_FP_FLAGS) $(MPFR_CFLAGS) -MMD -MP -c $< -o $@

$(CXX_OBJ_DIR)/analyze_rq2.o: analyze_rq2.cpp numerical_analysis.hpp \
        analysis_common.hpp | $(CXX_OBJ_DIR)
	$(CLANG_CXX) $(CXXFLAGS) $(STRICT_FP_FLAGS) $(MPFR_CFLAGS) -MMD -MP -c $< -o $@

$(CXX_OBJ_DIR)/analyze_rq3.o: analyze_rq3.cpp analysis_common.hpp \
                                      | $(CXX_OBJ_DIR)
	$(CLANG_CXX) $(CXXFLAGS) $(STRICT_FP_FLAGS) -MMD -MP -c $< -o $@

# --- C++ generation objects -----------------------------------------------
$(CXX_OBJ_DIR)/%.o: %.cpp | $(CXX_OBJ_DIR) check-dependencies
	$(CLANG_CXX) $(CXXFLAGS) $(STRICT_FP_FLAGS) $(FENCEDD_INC) $(QD_INC) $(MPFR_CFLAGS) \
	  -I. -MMD -MP -c $< -o $@

$(CXX_OBJ_DIR)/generate_performance_data_compcert.o: \
        generate_performance_data.cpp | $(CXX_OBJ_DIR) check-dependencies
	$(CLANG_CXX) $(CXXFLAGS) $(STRICT_FP_FLAGS) $(FENCEDD_INC) $(QD_INC) $(MPFR_CFLAGS) \
	  -I. -DFENCEDD_BUILD_LABEL=\"compcert\" -MMD -MP -c $< -o $@

$(CXX_OBJ_DIR)/generate_performance_data_clang.o: \
        generate_performance_data.cpp | $(CXX_OBJ_DIR) check-dependencies
	$(CLANG_CXX) $(CXXFLAGS) $(STRICT_FP_FLAGS) $(FENCEDD_INC) $(QD_INC) $(MPFR_CFLAGS) \
	  -I. -DFENCEDD_BUILD_LABEL=\"clang\" -MMD -MP -c $< -o $@

# --- benchmark links ------------------------------------------------------
$(BIN_DIR)/generate_numerical_data: $(NUMERICAL_DATA_OBJS) \
                                     $(COMPCERT_LIBRARY_OBJS) | $(BIN_DIR)
	$(CLANG_CXX) $(CXXFLAGS) $(STRICT_FP_FLAGS) -o $@ $^ $(MPFR_LIBS) -lm

$(BIN_DIR)/analyze_rq1: $(CXX_OBJ_DIR)/analyze_rq1.o \
                        $(CXX_OBJ_DIR)/numerical_analysis.o | $(BIN_DIR)
	$(CLANG_CXX) $(CXXFLAGS) $(STRICT_FP_FLAGS) -o $@ $^ $(MPFR_LIBS)

$(BIN_DIR)/analyze_rq2: $(CXX_OBJ_DIR)/analyze_rq2.o \
                        $(CXX_OBJ_DIR)/numerical_analysis.o | $(BIN_DIR)
	$(CLANG_CXX) $(CXXFLAGS) $(STRICT_FP_FLAGS) -o $@ $^ $(MPFR_LIBS)

$(BIN_DIR)/analyze_rq3: $(CXX_OBJ_DIR)/analyze_rq3.o | $(BIN_DIR)
	$(CLANG_CXX) $(CXXFLAGS) $(STRICT_FP_FLAGS) -o $@ $^

$(BIN_DIR)/generate_performance_data_compcert: \
        $(PERFORMANCE_COMPCERT_OBJS) $(COMPCERT_LIBRARY_OBJS) | $(BIN_DIR)
	$(CLANG_CXX) $(CXXFLAGS) $(STRICT_FP_FLAGS) -o $@ $^ $(MPFR_LIBS) -lm

$(BIN_DIR)/generate_performance_data_clang: \
        $(PERFORMANCE_CLANG_OBJS) $(CLANG_LIBRARY_OBJS) | $(BIN_DIR)
	$(CLANG_CXX) $(CXXFLAGS) $(STRICT_FP_FLAGS) -o $@ $^ $(MPFR_LIBS) -lm

# --- measurement and analysis workflow -----------------------------------
clean:
	rm -rf "$(BUILD_DIR)"

all-results:
	+$(MAKE) --no-print-directory raw-results RUN_DIR="$(RUN_PATH)"
	+$(MAKE) --no-print-directory analyze-results \
	  RUN_DIR="$(RUN_PATH)" ANALYSIS_DIR="$(ANALYSIS_DIR)"
	+$(MAKE) --no-print-directory tex-results \
	  RUN_DIR="$(RUN_PATH)" ANALYSIS_DIR="$(ANALYSIS_DIR)" TEX_DIR="$(TEX_DIR)"

raw-results: $(BIN_DIR)/generate_numerical_data \
             $(BIN_DIR)/generate_performance_data_compcert \
             $(BIN_DIR)/generate_performance_data_clang
	@test -n "$(RUN_PATH)" || { echo "RUN_DIR is required" >&2; exit 1; }
	mkdir -p "$(RUN_PATH)"
	@test ! -e "$(RUN_PATH)/numerical.tsv" || { echo "$(RUN_PATH)/numerical.tsv already exists" >&2; exit 1; }
	@test ! -e "$(RUN_PATH)/timing-compcert.tsv" || { echo "$(RUN_PATH)/timing-compcert.tsv already exists" >&2; exit 1; }
	@test ! -e "$(RUN_PATH)/timing-clang.tsv" || { echo "$(RUN_PATH)/timing-clang.tsv already exists" >&2; exit 1; }
	@test ! -e "$(RUN_PATH)/numerical.tsv.partial" || { echo "$(RUN_PATH)/numerical.tsv.partial already exists" >&2; exit 1; }
	@test ! -e "$(RUN_PATH)/timing-compcert.tsv.partial" || { echo "$(RUN_PATH)/timing-compcert.tsv.partial already exists" >&2; exit 1; }
	@test ! -e "$(RUN_PATH)/timing-clang.tsv.partial" || { echo "$(RUN_PATH)/timing-clang.tsv.partial already exists" >&2; exit 1; }
	$(BIN_DIR)/generate_numerical_data "$(SAMPLES_PER_EXPONENT)" "$(RUN_PATH)/numerical.tsv.partial"
	$(BIN_DIR)/generate_performance_data_compcert "$(NUM_INPUTS_FOR_PERF)" "$(NUM_TRIALS_FOR_PERF)" "$(RUN_PATH)/timing-compcert.tsv.partial"
	$(BIN_DIR)/generate_performance_data_clang "$(NUM_INPUTS_FOR_PERF)" "$(NUM_TRIALS_FOR_PERF)" "$(RUN_PATH)/timing-clang.tsv.partial"
	mv "$(RUN_PATH)/numerical.tsv.partial" "$(RUN_PATH)/numerical.tsv"
	mv "$(RUN_PATH)/timing-compcert.tsv.partial" "$(RUN_PATH)/timing-compcert.tsv"
	mv "$(RUN_PATH)/timing-clang.tsv.partial" "$(RUN_PATH)/timing-clang.tsv"

analyze-results: $(ANALYZERS)
	@test -f "$(RUN_PATH)/numerical.tsv" || { echo "$(RUN_PATH)/numerical.tsv not found" >&2; exit 1; }
	@test -f "$(RUN_PATH)/timing-compcert.tsv" || { echo "$(RUN_PATH)/timing-compcert.tsv not found" >&2; exit 1; }
	@test -f "$(RUN_PATH)/timing-clang.tsv" || { echo "$(RUN_PATH)/timing-clang.tsv not found" >&2; exit 1; }
	mkdir -p "$(ANALYSIS_DIR)"
	$(BIN_DIR)/analyze_rq1 "$(RUN_PATH)/numerical.tsv" \
	  "$(ANALYSIS_DIR)/rq1.tsv.partial"
	$(BIN_DIR)/analyze_rq2 "$(RUN_PATH)/numerical.tsv" \
	  "$(ANALYSIS_DIR)/rq2.tsv.partial"
	$(BIN_DIR)/analyze_rq3 "$(RUN_PATH)/timing-compcert.tsv" \
	  "$(RUN_PATH)/timing-clang.tsv" \
	  "$(ANALYSIS_DIR)/rq3.tsv.partial"
	mv "$(ANALYSIS_DIR)/rq1.tsv.partial" "$(ANALYSIS_DIR)/rq1.tsv"
	mv "$(ANALYSIS_DIR)/rq2.tsv.partial" "$(ANALYSIS_DIR)/rq2.tsv"
	mv "$(ANALYSIS_DIR)/rq3.tsv.partial" "$(ANALYSIS_DIR)/rq3.tsv"

tex-results:
	@test -f "$(ANALYSIS_DIR)/rq1.tsv" || { echo "$(ANALYSIS_DIR)/rq1.tsv not found" >&2; exit 1; }
	@test -f "$(ANALYSIS_DIR)/rq2.tsv" || { echo "$(ANALYSIS_DIR)/rq2.tsv not found" >&2; exit 1; }
	@test -f "$(ANALYSIS_DIR)/rq3.tsv" || { echo "$(ANALYSIS_DIR)/rq3.tsv not found" >&2; exit 1; }
	$(PYTHON) generate_paper_tables.py "$(ANALYSIS_DIR)" "$(TEX_DIR)"
	@echo "LaTeX table files: $(TEX_DIR)"

-include $(wildcard $(CXX_OBJ_DIR)/*.d $(COMPCERT_OBJ_DIR)/*.d \
                   $(CLANG_OBJ_DIR)/*.d)
