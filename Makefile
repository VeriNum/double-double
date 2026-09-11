# Benchmark targets are handled by bench/Makefile rather than CoqMakefile.
BENCHTARGETS := all-results raw-results analyze-results tex-results
PROOFTARGETS := accuracy verification

# KNOWNTARGETS will not be passed along to CoqMakefile
KNOWNTARGETS := CoqMakefile AccuracyMakefile extra-stuff extra-stuff2
KNOWNTARGETS += $(BENCHTARGETS) $(PROOFTARGETS)
# KNOWNFILES will not get implicit targets from the final rule, and so
# depending on them won't invoke the submake
# Warning: These files get declared as PHONY, so any targets depending
# on them always get rebuilt
KNOWNFILES   := Makefile _CoqProject _CoqProject.accuracy

.DEFAULT_GOAL := invoke-coqmakefile

ifneq ($(MAKECMDGOALS),run-clightgen)
ifneq ($(MAKECMDGOALS),clean)
.SECONDEXPANSION:
CoqMakefile: Makefile _CoqProject $$(CLIGHT_FILES)
	$(COQBIN)coq_makefile -f _CoqProject -o CoqMakefile

AccuracyMakefile: Makefile _CoqProject.accuracy
	$(COQBIN)coq_makefile -f _CoqProject.accuracy -o AccuracyMakefile

invoke-coqmakefile: CoqMakefile
	$(MAKE) --no-print-directory -f CoqMakefile $(filter-out $(KNOWNTARGETS),$(MAKECMDGOALS))

.PHONY: invoke-coqmakefile $(KNOWNFILES)
endif
endif
####################################################################
##                      Your targets here                         ##
####################################################################

.PHONY: $(PROOFTARGETS)
accuracy: AccuracyMakefile
	$(MAKE) --no-print-directory -f AccuracyMakefile

verification: invoke-coqmakefile

.PHONY: $(BENCHTARGETS)
$(BENCHTARGETS):
	@test -n "$(RUN_DIR)" || { echo "usage: make $@ RUN_DIR=results/" >&2; exit 1; }
	+$(MAKE) --no-print-directory -C bench $@ RUN_DIR="$(abspath $(RUN_DIR))"

SRCDIR = fenceDD
OBJDIR = verif_proofs/verif_objs
INCLUDES = -I $(SRCDIR)/include
CLIGHT_HEADERS = $(SRCDIR)/include/dw_arith.h $(SRCDIR)/include/fp_utils.h
CLIGHT_FILES = $(OBJDIR)/fp_utils.v $(OBJDIR)/dd_ops.v

# dd_ops.c includes every library source except fp_utils.c. A change to any
# included source must therefore regenerate the single dd_ops Clight file.
DD_OPS_SOURCES = $(filter-out $(SRCDIR)/example.c $(SRCDIR)/fp_utils.c \
	$(SRCDIR)/two_sum_test.c,$(wildcard $(SRCDIR)/*.c))

.PHONY: run-clightgen
run-clightgen: $(CLIGHT_FILES)

$(OBJDIR):
	mkdir -p $@

$(CLIGHT_FILES): $(CLIGHT_HEADERS) | $(OBJDIR)

$(OBJDIR)/fp_utils.v: $(SRCDIR)/fp_utils.c
	clightgen -normalize $(INCLUDES) $< -o $@

$(OBJDIR)/dd_ops.v: $(DD_OPS_SOURCES)
	clightgen -normalize $(INCLUDES) $(SRCDIR)/dd_ops.c -o $@

.PHONY: clean
clean:
	rm -f CoqMakefile CoqMakefile.conf .CoqMakefile.d
	rm -f AccuracyMakefile AccuracyMakefile.conf .AccuracyMakefile.d
	rm -f $(CLIGHT_FILES)
	find . -name .git -prune -o -type f \
		\( -name '*.vo' -o -name '*.vos' -o -name '*.vok' -o -name '*.glob' -o -name '.*.aux' \) \
		-exec rm -f {} +

# This should be the last rule, to handle any targets not declared above
ifneq ($(MAKECMDGOALS),run-clightgen)
ifneq ($(MAKECMDGOALS),clean)
%: invoke-coqmakefile
	@true
endif
endif
