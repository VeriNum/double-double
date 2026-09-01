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
#   QD_PREFIX   install prefix containing the qd/ headers       (default: discovered)
#   QD_CONFIG   qd-config executable used for discovery         (default: qd-config on PATH)
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

DD_CC      ?= ccomp
CLANG_CC   ?= clang
CXX        ?= g++
DD_CFLAGS  ?= -O3
CLANG_CFLAGS ?= -O3 -std=c11
CXXFLAGS   ?= -O3 -std=c++14 -Wall
STRICT_FP_FLAGS := -fno-fast-math -ffp-contract=off
PKG_CONFIG ?= pkg-config
PYTHON     ?= python3

# An explicit QD_PREFIX or QD_CONFIG is authoritative. Without either, the
# resolver searches the artifact-local prefix and installed candidates.
ifeq ($(origin QD_PREFIX), undefined)
  ifeq ($(origin QD_CONFIG), undefined)
    QD_DISCOVERY_ARGS :=
  else
    QD_DISCOVERY_ARGS := --qd-config "$(QD_CONFIG)"
  endif
  QD_PREFIX := $(shell $(PYTHON) find_qd.py --prefix-only \
                 $(QD_DISCOVERY_ARGS) 2>/dev/null)
else
  QD_DISCOVERY_ARGS := --prefix "$(QD_PREFIX)"
endif

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
BUILD_CONFIG := $(BUILD_DIR)/config.json
CLANG_BUILD_DIR := $(BUILD_DIR)/clang

RUN_ROOT ?= runs
ifeq ($(origin RUN_ID), undefined)
RUN_ID := $(shell date -u +%Y%m%dT%H%M%SZ)
endif
PROFILE ?= artifact
RUN_DIR ?= $(RUN_ROOT)/$(RUN_ID)
GENERATED_DIR ?= $(RUN_DIR)/generated

export DD_CC DD_CFLAGS CLANG_CC CLANG_CFLAGS CXX CXXFLAGS STRICT_FP_FLAGS \
       QD_PREFIX PKG_CONFIG

EVALUATIONS := rq1_accuracy rq2_guard_acceptance \
               rq3_performance_compcert rq3_performance_clang
EXAMPLES   := multiplication_underflow_example
TESTS      := test_input_generation test_interface_runner test_mpfr_bounds \
              test_accuracy_metrics
ALL_BINS   := $(EVALUATIONS) $(EXAMPLES) $(TESTS)

# Arithmetic-only kernel baseline.  Keep wrapper and kernel objects distinct:
# the public dw_*.c files do not define their corresponding *_kernel symbols.
EFT_SRCS     := two_sum fast_2sum fast_2mult
DW_OPS       := dw_plus_fp dw_plus_dw dw_times_fp dw_times_dw dw_div_fp dw_div_dw
KERNEL_SRCS  := $(EFT_SRCS) $(addsuffix _kernel,$(DW_OPS))
KERNEL_OBJS  := $(addsuffix .o,$(KERNEL_SRCS))

# The six dw_*.c files define both the default (two-stage) and strong
# (input-only) interfaces. The exact transformations have one guarded entry
# point each.
LIBRARY_SRCS := $(KERNEL_SRCS) two_sum_guarded fast_2sum_guarded \
                fast_2mult_guarded fp_utils $(DW_OPS)
LIBRARY_OBJS := $(addsuffix .o,$(LIBRARY_SRCS))
CLANG_LIBRARY_OBJS := $(addprefix $(CLANG_BUILD_DIR)/,\
                        $(addsuffix .o,$(LIBRARY_SRCS)))

EVAL_COMMON_OBJS := input_generation.o
RQ1_OBJS := rq1_accuracy.o mpfr_accuracy.o $(EVAL_COMMON_OBJS)
RQ2_OBJS := rq2_guard_acceptance.o boundary_cases.o mpfr_accuracy.o \
            $(EVAL_COMMON_OBJS)
RQ3_COMPCERT_OBJS := $(BUILD_DIR)/rq3_performance_compcert.o $(EVAL_COMMON_OBJS)
RQ3_CLANG_OBJS := $(BUILD_DIR)/rq3_performance_clang.o $(EVAL_COMMON_OBJS)

# Sources needed by the constructed multiplication-underflow example.
MUL_EXAMPLE_OBJS := fast_2mult.o fast_2sum.o fast_2mult_guarded.o \
                    fp_utils.o dw_times_dw_kernel.o dw_times_dw.o

all: $(EVALUATIONS)

build: all

.PHONY: FORCE check-dependencies
FORCE:

check-dependencies:
	@test -f "$(DD_LIB_DIR)/include/dw_arith.h" || { \
	  echo "dd_lib headers not found under $(DD_LIB_DIR)" >&2; \
	  echo "Set DD_LIB_DIR to the dd_lib source directory." >&2; \
	  exit 1; \
	}
	@$(PYTHON) find_qd.py --prefix-only $(QD_DISCOVERY_ARGS) >/dev/null

$(BUILD_DIR):
	mkdir -p $@

$(CLANG_BUILD_DIR): | $(BUILD_DIR)
	mkdir -p $@

$(BUILD_CONFIG): FORCE write_build_config.py find_qd.py qd_evaluation.hpp | $(BUILD_DIR) check-dependencies
	$(PYTHON) write_build_config.py $@ \
	  --dd-cc="$(DD_CC)" --dd-cflags="$(DD_CFLAGS)" \
	  --clang-cc="$(CLANG_CC)" --clang-cflags="$(CLANG_CFLAGS)" \
	  --cxx="$(CXX)" --cxxflags="$(CXXFLAGS)" \
	  --strict-fp-flags="$(STRICT_FP_FLAGS)" --qd-prefix="$(QD_PREFIX)" \
	  --mpfr-cflags="$(MPFR_CFLAGS)" --mpfr-libs="$(MPFR_LIBS)"

# --- dd_lib objects: generic rule (one .o per dd_lib .c) ------------------
%.o: $(DD_LIB_DIR)/%.c $(DD_LIB_DIR)/include/dw_arith.h $(BUILD_CONFIG)
	$(DD_CC) $(DD_CFLAGS) $(DD_INC) -c $< -o $@

$(addsuffix .o,two_sum_guarded fast_2sum_guarded fast_2mult_guarded fp_utils $(DW_OPS)): \
  $(DD_LIB_DIR)/include/fp_utils.h

$(CLANG_BUILD_DIR)/%.o: $(DD_LIB_DIR)/%.c \
                        $(DD_LIB_DIR)/include/dw_arith.h $(BUILD_CONFIG) \
                        | $(CLANG_BUILD_DIR)
	$(CLANG_CC) $(CLANG_CFLAGS) $(STRICT_FP_FLAGS) $(DD_INC) -c $< -o $@

$(addprefix $(CLANG_BUILD_DIR)/,\
  $(addsuffix .o,two_sum_guarded fast_2sum_guarded fast_2mult_guarded fp_utils $(DW_OPS))): \
  $(DD_LIB_DIR)/include/fp_utils.h

# --- C++ evaluation objects -----------------------------------------------
%.o: %.cpp $(BUILD_CONFIG) | check-dependencies
	$(CXX) $(CXXFLAGS) $(STRICT_FP_FLAGS) $(DD_INC) $(QD_INC) $(MPFR_CFLAGS) \
	  -I. -MMD -MP -c $< -o $@

tests/%.o: tests/%.cpp $(BUILD_CONFIG) | check-dependencies
	$(CXX) $(CXXFLAGS) $(STRICT_FP_FLAGS) $(DD_INC) $(QD_INC) $(MPFR_CFLAGS) \
	  -I. -MMD -MP -c $< -o $@

$(BUILD_DIR)/rq3_performance_compcert.o: rq3_performance.cpp $(BUILD_CONFIG) \
                                        | check-dependencies
	$(CXX) $(CXXFLAGS) $(STRICT_FP_FLAGS) $(DD_INC) $(QD_INC) $(MPFR_CFLAGS) \
	  -I. -DDD_BUILD_LABEL=\"compcert\" -MMD -MP -c $< -o $@

$(BUILD_DIR)/rq3_performance_clang.o: rq3_performance.cpp $(BUILD_CONFIG) \
                                     | check-dependencies
	$(CXX) $(CXXFLAGS) $(STRICT_FP_FLAGS) $(DD_INC) $(QD_INC) $(MPFR_CFLAGS) \
	  -I. -DDD_BUILD_LABEL=\"clang\" -MMD -MP -c $< -o $@

# --- evaluation links -----------------------------------------------------
rq1_accuracy: $(RQ1_OBJS) $(LIBRARY_OBJS)
	$(CXX) $(CXXFLAGS) $(STRICT_FP_FLAGS) -o $@ $^ $(MPFR_LIBS) -lm

rq2_guard_acceptance: $(RQ2_OBJS) $(LIBRARY_OBJS)
	$(CXX) $(CXXFLAGS) $(STRICT_FP_FLAGS) -o $@ $^ $(MPFR_LIBS) -lm

rq3_performance_compcert: $(RQ3_COMPCERT_OBJS) $(LIBRARY_OBJS)
	$(CXX) $(CXXFLAGS) $(STRICT_FP_FLAGS) -o $@ $^ $(MPFR_LIBS) -lm

rq3_performance_clang: $(RQ3_CLANG_OBJS) $(CLANG_LIBRARY_OBJS)
	$(CXX) $(CXXFLAGS) $(STRICT_FP_FLAGS) -o $@ $^ $(MPFR_LIBS) -lm

test_input_generation: tests/test_input_generation.o input_generation.o
	$(CXX) $(CXXFLAGS) $(STRICT_FP_FLAGS) -o $@ $^ $(MPFR_LIBS) -lm

test_interface_runner: tests/test_interface_runner.o
	$(CXX) $(CXXFLAGS) $(STRICT_FP_FLAGS) -o $@ $^

test_mpfr_bounds: tests/test_mpfr_bounds.o mpfr_accuracy.o
	$(CXX) $(CXXFLAGS) $(STRICT_FP_FLAGS) -o $@ $^ $(MPFR_LIBS) -lm

test_accuracy_metrics: tests/test_accuracy_metrics.o mpfr_accuracy.o
	$(CXX) $(CXXFLAGS) $(STRICT_FP_FLAGS) -o $@ $^ $(MPFR_LIBS) -lm

# Constructed case showing the difference between the mixed DWTimesDW contract
# and the exact-reconstruction Fast2Mult contract. It is not part of `all`.
multiplication_underflow_example: multiplication_underflow_example.o $(MUL_EXAMPLE_OBJS)
	$(CXX) $(CXXFLAGS) $(STRICT_FP_FLAGS) -o $@ $^ $(MPFR_LIBS) -lm

# --- validation and evaluation workflow ----------------------------------
.PHONY: all build clean check prepare-evaluation smoke results run-evaluation \
        report-evaluation check-report \
        run-rq1 run-rq2 run-rq3 run-multiplication-example
clean:
	rm -f *.o *.d tests/*.o tests/*.d $(ALL_BINS)
	rm -f rq3_performance $(BUILD_CONFIG) $(BUILD_DIR)/rq3_performance_*.o \
	      $(BUILD_DIR)/rq3_performance_*.d
	rm -rf $(CLANG_BUILD_DIR)
	rmdir $(BUILD_DIR) 2>/dev/null || true

check: $(EVALUATIONS) $(TESTS)
	./test_input_generation
	./test_interface_runner
	./test_mpfr_bounds
	./test_accuracy_metrics
	./rq2_guard_acceptance --boundary-only
	$(PYTHON) tests/test_run_evaluation.py
	$(PYTHON) tests/test_reporting.py
	$(PYTHON) tests/test_find_qd.py

prepare-evaluation: all check

smoke: prepare-evaluation
	$(PYTHON) run_evaluation.py --profile smoke --run-id "$(RUN_ID)" \
	  --run-root "$(RUN_ROOT)" --bin-dir . --repo-root .. \
	  --dd-cc="$(DD_CC)" --dd-cflags="$(DD_CFLAGS)" \
	  --clang-cc="$(CLANG_CC)" --clang-cflags="$(CLANG_CFLAGS)" \
	  --cxx="$(CXX)" --cxxflags="$(CXXFLAGS)" \
	  --strict-fp-flags="$(STRICT_FP_FLAGS)" \
	  --qd-prefix="$(QD_PREFIX)" --pkg-config="$(PKG_CONFIG)"
	$(PYTHON) generate_reports.py "$(RUN_DIR)" \
	  --output-dir "$(GENERATED_DIR)"

results:
	+$(MAKE) --no-print-directory run-evaluation \
	  PROFILE=artifact RUN_ID="$(RUN_ID)"
	+$(MAKE) --no-print-directory report-evaluation RUN_ID="$(RUN_ID)"
	@echo "Full evaluation report: $(GENERATED_DIR)/RESULTS.md"

run-evaluation: prepare-evaluation
	$(PYTHON) run_evaluation.py --profile "$(PROFILE)" --run-id "$(RUN_ID)" \
	  --run-root "$(RUN_ROOT)" --bin-dir . --repo-root .. \
	  --dd-cc="$(DD_CC)" --dd-cflags="$(DD_CFLAGS)" \
	  --clang-cc="$(CLANG_CC)" --clang-cflags="$(CLANG_CFLAGS)" \
	  --cxx="$(CXX)" --cxxflags="$(CXXFLAGS)" \
	  --strict-fp-flags="$(STRICT_FP_FLAGS)" \
	  --qd-prefix="$(QD_PREFIX)" --pkg-config="$(PKG_CONFIG)"

report-evaluation:
	$(PYTHON) generate_reports.py "$(RUN_DIR)" \
	  --output-dir "$(GENERATED_DIR)"

check-report:
	$(PYTHON) generate_reports.py "$(RUN_DIR)" \
	  --output-dir "$(GENERATED_DIR)" --check

run-rq1: rq1_accuracy
	./rq1_accuracy

run-rq2: rq2_guard_acceptance
	./rq2_guard_acceptance

run-rq3: rq3_performance_compcert rq3_performance_clang
	./rq3_performance_compcert
	./rq3_performance_clang

run-multiplication-example: multiplication_underflow_example
	./multiplication_underflow_example

-include $(wildcard *.d tests/*.d $(BUILD_DIR)/*.d)
