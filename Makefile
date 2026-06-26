# graph-theory-rocq root build. Each package has a _CoqProject; we generate its Makefile.coq
# and build, in dependency order (base first; area packages depend on base).
PACKAGES := base chromatic-theory hamiltonicity-theory homomorphism-theory
.PHONY: all clean $(PACKAGES)
all: $(PACKAGES)

chromatic-theory hamiltonicity-theory homomorphism-theory: base   # area packages depend on base (G3-core)

$(PACKAGES):
	cd $@ && rocq makefile -f _CoqProject -o Makefile.coq && $(MAKE) -f Makefile.coq

clean:
	@for p in $(PACKAGES); do (cd $$p && rocq makefile -f _CoqProject -o Makefile.coq >/dev/null 2>&1 && $(MAKE) -f Makefile.coq clean) 2>/dev/null || true; done

# NOTE: `base/` (G3-core) + `chromatic-theory/` (U1) build today; add each area package to
# PACKAGES (with `<pkg>: base`) as its milestone lands. The absorbed `digraph-theory/` builds
# via its own Makefile (heavy proofs) and is intentionally out of the default `all`.
