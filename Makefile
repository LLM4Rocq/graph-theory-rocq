# graph-theory-rocq root build — recurses into each package (coq_makefile per package).
PACKAGES := base digraph-theory
.PHONY: all clean $(PACKAGES)
all: $(PACKAGES)
$(PACKAGES):
	$(MAKE) -C $@
clean:
	@for p in $(PACKAGES); do $(MAKE) -C $$p clean 2>/dev/null || true; done
# NOTE (G0): only `base` (G3) and the absorbed `digraph-theory` build today; area packages
# are added to PACKAGES as each milestone lands (see meta/OPG_FULL_FORMALIZATION_PLAN.md §7).
