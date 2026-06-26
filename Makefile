# graph-theory-rocq root build. Each package has a _CoqProject; we generate its Makefile.coq
# and build, in dependency order (base first; area packages depend on base).
PACKAGES := base chromatic-theory hamiltonicity-theory homomorphism-theory cycle-theory minor-theory packing-theory reconstruction-theory hypergraph-theory topological-graph-theory
LANDED := U1 chromatic-theory U2 hamiltonicity-theory U3 homomorphism-theory U4 chromatic-theory U5 chromatic-theory U6 cycle-theory U7 minor-theory U8 chromatic-theory U9 packing-theory U10 cycle-theory U11 reconstruction-theory U12 hypergraph-theory U13 topological-graph-theory
.PHONY: all clean gate $(PACKAGES)
all: $(PACKAGES)

chromatic-theory hamiltonicity-theory homomorphism-theory cycle-theory minor-theory packing-theory reconstruction-theory hypergraph-theory topological-graph-theory: base   # area packages depend on base (G3-core)

# CI gate (G1 + acceptance): manifest reproduces, edge-graph has no drift, every landed
# milestone passes check_milestone (compiles, axiom-free, Print-Assumptions-clean, legs justified).
gate:
	python3 meta/build_opg_manifest.py
	python3 meta/build_edge_graph.py --check
	@set -e; set -- $(LANDED); while [ $$# -ge 2 ]; do python3 meta/check_milestone.py $$1 $$2; shift 2; done

$(PACKAGES):
	cd $@ && rocq makefile -f _CoqProject -o Makefile.coq && $(MAKE) -f Makefile.coq

clean:
	@for p in $(PACKAGES); do (cd $$p && rocq makefile -f _CoqProject -o Makefile.coq >/dev/null 2>&1 && $(MAKE) -f Makefile.coq clean) 2>/dev/null || true; done

# NOTE: `base/` (G3-core) + `chromatic-theory/` (U1) build today; add each area package to
# PACKAGES (with `<pkg>: base`) as its milestone lands. The absorbed `digraph-theory/` builds
# via its own Makefile (heavy proofs) and is intentionally out of the default `all`.
