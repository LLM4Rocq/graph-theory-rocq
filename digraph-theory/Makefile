# Thin wrapper delegating to a Makefile.coq generated from _CoqProject.
# (Standard coq-community pattern. Works with `coq_makefile` / `rocq makefile`.)

# Targets handled here, never forwarded to Makefile.coq:
KNOWNTARGETS := Makefile.coq
# Files that must never be treated as build targets:
KNOWNFILES   := Makefile _CoqProject

.DEFAULT_GOAL := invoke-coqmakefile

Makefile.coq: Makefile _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq $(EXTRA_DIR_OPTS)

invoke-coqmakefile: Makefile.coq
	$(MAKE) --no-print-directory -f Makefile.coq $(filter-out $(KNOWNTARGETS),$(MAKECMDGOALS))

clean:: Makefile.coq
	$(MAKE) --no-print-directory -f Makefile.coq cleanall
	rm -f Makefile.coq Makefile.coq.conf

.PHONY: invoke-coqmakefile clean $(KNOWNFILES)

####################################################################
##                      Project-specific targets                  ##
####################################################################

# (none yet)

# Catch-all: forward any other target to Makefile.coq.
%: invoke-coqmakefile
	@true
