# `theories/` — intended layout

Logical root: `Digraph` (`-R theories Digraph`). Because `From Digraph Require
Import x.` matches by suffix, files are imported by their bare name regardless of
subdirectory, e.g. `From Digraph Require Import prelude tournament omegabar.`

Lower layers never depend on higher ones. Only `foundations/interop_graph_theory.v`
imports `coq-graph-theory`. Full rationale and signatures: [`../docs/DESIGN.md`](../docs/DESIGN.md).

```
foundations/
  prelude.v                  # M0 ✅  classical baseline + MathComp imports
  interop_graph_theory.v     # M0 stub → M1  single bridge to coq-graph-theory (ω/α/χ)
core/
  digraph.v                  # M1  digraph as a relation; converse, induced, deletion
  tournament.v               # M1  HB structure: irreflexive + total; N+/N-, beats
  order.v                    # M1  orders as {perm V}; backedge graph T^p : sgraph
invariants/
  omegabar.v                 # M1  ω̄ = min over {perm V} of ω(T^p); monotonicity
  critical.v                 # M1  k-ω̄-critical; deletion behaviour
  domination.v               # M3  digraph domination; dom ≤ ω̄
  dichromatic.v              # M3  χ̄; ω̄ ≤ χ̄; χ-boundedness vocabulary
constructions/
  product.v                  # M2  lexicographic substitution S[H]
  cayley.v                   # M2  Cayley digraph Cay(G,S); tournament iff S ⊍ -S = G\{e}
  circulant.v                # M2  specialisation to 'Z_n; ACₙ
  automorphism.v             # M2  Aut(D); group action; vertex_transitive
invariants_advanced/
  substitution.v             # M3  ω̄(S[H]) ≥ ω̄(S)+ω̄(H)-1
  transitive.v               # M3  vertex-transitive ⇒ ω̄(T-v) uniform
applications/k5/
  acn_arc_facts.v            # M4  g={1..m-1}∪{m+1}; arc-facts (i)-(iii)
  acn_base.v                 # M4  ω̄(ACₙ)=3, unique triangle, autocorrelation, 3-critical
  in_neighbourhood.v         # M6  Lemma H17 (common in-nbhd in one band)
  cells.v                    # M6  8 cells, one-vertex-per-cell, band caps
  obstructions.v             # M6  the 20 infeasible cell-sets
  coverage.v                 # M6  every 5-subset hits one of the 20 (by reflection)
  main.v                     # M6  ω̄=5, 5-ω̄-critical; Conj 5.10 @ k=5; Q5.9 fails
```

Only `foundations/` exists at M0; later directories are added per milestone and
registered in `../_CoqProject` as their files land.
