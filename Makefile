# KNOWNTARGETS will not be passed along to CoqMakefile
KNOWNTARGETS := CoqMakefile extra-stuff extra-stuff2
# KNOWNFILES will not get implicit targets from the final rule, and so
# depending on them won't invoke the submake
# Warning: These files get declared as PHONY, so any targets depending
# on them always get rebuilt
KNOWNFILES   := Makefile _CoqProject

.DEFAULT_GOAL := invoke-coqmakefile

ifneq ($(MAKECMDGOALS),run-clightgen)
ifneq ($(MAKECMDGOALS),clean)
CoqMakefile: Makefile _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o CoqMakefile

invoke-coqmakefile: CoqMakefile
	$(MAKE) --no-print-directory -f CoqMakefile $(filter-out $(KNOWNTARGETS),$(MAKECMDGOALS))

.PHONY: invoke-coqmakefile $(KNOWNFILES)
endif
endif
####################################################################
##                      Your targets here                         ##
####################################################################

OBJDIR = verif_proofs/verif_objs
OBJ = two_sum.v fast_2mult.v fast_2sum.v
OBJ += dw_plus_fp.v dw_plus_dw.v
OBJ += dw_mult_fp.v dw_mult_dw.v
OBJS = $(addprefix $(OBJDIR)/,$(OBJ))
SRCDIR = dd_lib
INCLUDES = -I $(SRCDIR)/include

run-clightgen: $(OBJS)
	
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

