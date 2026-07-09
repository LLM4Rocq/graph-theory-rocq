# graph-theory-rocq root build. Each package has a _CoqProject; we generate its Makefile.coq
# and build, in dependency order (base first; area packages depend on base).
PACKAGES := base chromatic-theory hamiltonicity-theory homomorphism-theory cycle-theory minor-theory packing-theory reconstruction-theory hypergraph-theory topological-graph-theory graph-theory-misc spectral-graph-theory extremal-graph-theory infinite-graph-theory
LANDED := U1 chromatic-theory U2 hamiltonicity-theory U3 homomorphism-theory U4 chromatic-theory U5 chromatic-theory U6 cycle-theory U7 minor-theory U8 chromatic-theory U9 packing-theory U10 cycle-theory D1 cycle-theory D7 graph-theory-misc D5 spectral-graph-theory D2chr extremal-graph-theory D2ram extremal-graph-theory D2tur extremal-graph-theory D2pr extremal-graph-theory D2str extremal-graph-theory D3cr topological-graph-theory D3geo topological-graph-theory D3xseq topological-graph-theory D4doa infinite-graph-theory D4inf1 infinite-graph-theory D4inf2 infinite-graph-theory D4inf3 infinite-graph-theory D4inf4 infinite-graph-theory D4inf5 infinite-graph-theory D6emb topological-graph-theory U11 reconstruction-theory U12 hypergraph-theory U13 topological-graph-theory U13 packing-theory U13 graph-theory-misc P9 digraph-theory X1 digraph-theory X2 digraph-theory X3 chromatic-theory X4 extremal-graph-theory X5 minor-theory X5 cycle-theory X5 packing-theory X5 hamiltonicity-theory X6 hypergraph-theory X6 spectral-graph-theory X6 topological-graph-theory XE1 chromatic-theory XE2 chromatic-theory XE1 cycle-theory XE2 cycle-theory XE1 graph-theory-misc XE2 graph-theory-misc XE1 hypergraph-theory XE2 hypergraph-theory XE1 packing-theory XE2 digraph-theory XE1 extremal-graph-theory XE2 extremal-graph-theory
.PHONY: all clean gate audit mutation $(PACKAGES)
all: $(PACKAGES)

chromatic-theory hamiltonicity-theory homomorphism-theory cycle-theory minor-theory packing-theory reconstruction-theory hypergraph-theory topological-graph-theory graph-theory-misc spectral-graph-theory extremal-graph-theory infinite-graph-theory: base   # area packages depend on base (G3-core)

hamiltonicity-theory packing-theory: topological-graph-theory   # Wave-1: use the embedding foundation

# CI gate (G1 + acceptance): manifest reproduces, edge-graph has no drift, every landed
# milestone passes check_milestone (compiles, axiom-free, Print-Assumptions-clean, legs justified).
gate:
	python3 meta/build_opg_manifest.py
	python3 meta/build_edge_graph.py --check
	python3 meta/report_corpus_status.py --check
	@set -e; set -- $(LANDED); while [ $$# -ge 2 ]; do python3 meta/check_milestone.py $$1 $$2; shift 2; done

# Toolchain-free status audit (no Coq build, no external OPG source) — backs the
# "statement-complete" claim in CI. Only VERIFIES the committed manifest/overlay/report/edge-graph
# are mutually consistent (drift + invariants); it does NOT regenerate the manifest, since
# build_opg_manifest.py reads the external OpenProblemGarden clone (data/problems.json) which is
# not in the repo. Manifest regeneration lives in `gate`, run in the full dev environment.
audit:
	python3 meta/build_edge_graph.py --check
	python3 meta/report_corpus_status.py --check

mutation:
	python3 meta/faithfulness_mutation.py

$(PACKAGES):
	cd $@ && rocq makefile -f _CoqProject -o Makefile.coq && $(MAKE) -f Makefile.coq

clean:
	@for p in $(PACKAGES); do (cd $$p && rocq makefile -f _CoqProject -o Makefile.coq >/dev/null 2>&1 && $(MAKE) -f Makefile.coq clean) 2>/dev/null || true; done

# NOTE: `base/` (G3-core) + `chromatic-theory/` (U1) build today; add each area package to
# PACKAGES (with `<pkg>: base`) as its milestone lands. The absorbed `digraph-theory/` (heavy
# proofs) is kept out of the default `all`/`PACKAGES` to keep `make all` light — but its P9
# milestone IS gated: `make gate` runs `check_milestone P9 digraph-theory` (it builds the package
# itself, verifies all 32 formal_names Defined + axiom-free + Print Assumptions clean). The
# already-formalized P9 rows live in sibling conjecture files (classic_core.v/packing.v/sad.v/
# colouring_variants.v/long_dipath.v) which check_milestone now scans + imports.
