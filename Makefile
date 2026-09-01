# Evaluation targets are handled by bench/Makefile rather than CoqMakefile.
BENCHTARGETS := prepare-evaluation smoke results run-evaluation report-evaluation \
                check-report \
                multiplication_underflow_example

# KNOWNTARGETS will not be passed along to CoqMakefile
KNOWNTARGETS := CoqMakefile extra-stuff extra-stuff2 $(BENCHTARGETS)
# KNOWNFILES will not get implicit targets from the final rule, and so
# depending on them won't invoke the submake
# Warning: These files get declared as PHONY, so any targets depending
# on them always get rebuilt
KNOWNFILES   := Makefile _CoqProject

.DEFAULT_GOAL := invoke-coqmakefile

ifneq ($(MAKECMDGOALS),run-clightgen)
ifneq ($(MAKECMDGOALS),clean)
.SECONDEXPANSION:
CoqMakefile: Makefile _CoqProject $$(OBJS)
	$(COQBIN)coq_makefile -f _CoqProject -o CoqMakefile

invoke-coqmakefile: CoqMakefile
	$(MAKE) --no-print-directory -f CoqMakefile $(filter-out $(KNOWNTARGETS),$(MAKECMDGOALS))

.PHONY: invoke-coqmakefile $(KNOWNFILES)
endif
endif
####################################################################
##                      Your targets here                         ##
####################################################################

.PHONY: $(BENCHTARGETS)
$(BENCHTARGETS):
	+$(MAKE) --no-print-directory -C bench $@

OBJDIR = verif_proofs/verif_objs
OBJ = two_sum.v two_sum_guarded.v fast_2mult.v fast_2mult_guarded.v fast_2mult_acc_guarded.v fast_2sum.v fast_2sum_guarded.v
OBJ += dw_plus_fp_kernel.v dw_plus_fp.v dw_plus_dw_kernel.v dw_plus_dw.v
OBJ += dw_times_fp_kernel.v dw_times_fp.v dw_times_dw_kernel.v dw_times_dw.v
OBJ += dw_div_fp_kernel.v dw_div_fp.v dw_div_dw_kernel.v dw_div_dw.v
OBJ += fp_utils.v
# dd_ops.c is an aggregation unit (#includes the op + guarded .c files) so the
# whole operations translation unit compiles to one Clight program / CompSpecs.
OBJ += dd_ops.v
OBJS = $(addprefix $(OBJDIR)/,$(OBJ))
SRCDIR = dd_lib
INCLUDES = -I $(SRCDIR)/include
CLIGHT_HEADERS = $(SRCDIR)/include/dw_arith.h $(SRCDIR)/include/fp_utils.h
CLIGHT_SOURCES = $(addprefix $(SRCDIR)/,$(OBJ:.v=.c))
DD_OPS_INCLUDES = $(filter-out $(SRCDIR)/fp_utils.c $(SRCDIR)/dd_ops.c,$(CLIGHT_SOURCES))

.PHONY: run-clightgen
run-clightgen: $(OBJS)
	
$(OBJDIR):
	mkdir -p $@

$(OBJS): $(CLIGHT_HEADERS) | $(OBJDIR)

$(OBJDIR)/dd_ops.v: $(DD_OPS_INCLUDES)

$(OBJS): $(OBJDIR)/%.v: $(SRCDIR)/%.c
	clightgen -normalize $(INCLUDES) $< -o $@

clean:
	rm -f CoqMakefile CoqMakefile.conf
	rm -f *.vo *.vos *.vok *.glob
	rm -f paper_proofs/*.{vo,vos,vok,glob}
	rm -f common/*.vo
	rm -f verif_objs/*.{vo,vos,vok,glob}

# This should be the last rule, to handle any targets not declared above
%: invoke-coqmakefile
	@true
