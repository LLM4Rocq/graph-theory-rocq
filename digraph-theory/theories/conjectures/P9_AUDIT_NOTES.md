# digraph-theory / P9 — directed-conjectures audit notes

P9 = the directed phase. Of the 32 manifest rows, **12 are already-formalized** (a pre-existing
bridge in `classic_core`/`packing`/`sad`/`long_dipath`/`colouring_variants`.v — recorded `done`, NOT
restated); this milestone adds the **20 NEW rows** in `theories/conjectures/P9.v`. Carrier = the
directed `diGraph` (coq-graph-theory), reusing the repo's own core (no GTBase). Verified: P9.v +
grounding_P9.v (35/35 `Qed`) + implications_P9.v compile in the monorepo; Print Assumptions = "Closed
under the global context" (axiom-free). **Leg state: 20 done, 0 blocked.**

## MAJOR FINDING — the 3 "planar" rows are NOT G2-blocked
The agent reused **`planar_sg` from `two_extremal.v`**: combinatorial **Wagner/Kuratowski** planarity,
`planar_sg G := ~ sg_minor G 'K_5 /\ ~ sg_minor G 'K_3,3`, which compiles **without
coq-graph-theory-planar / coq-fourcolor**. By Wagner's theorem this is *exactly* planarity, so
`partitioning_planar_digraphs`, `oriented_chromatic_number_of_planar_graphs`, and
`large_acyclic_induced_subdigraph_in_a_planar_oriented_graph` are stated with **real planarity of the
underlying simple graph, axiom-free** — **done, not blocked.** (Orientation = `diGraph D` + loopless +
no-digons; the underlying simple graph via `underlyingG`.)

➜ **Strategic implication (for review):** the 14 currently G2-blocked *undirected* planar rows that
need only "G is planar" (not a face/embedding/genus notion) could likewise be unblocked by promoting
a combinatorial `planar` (K5/K3,3-minor-free) predicate to base — **no fourcolor needed**. Rows that
genuinely need an embedding/faces (plane-triangulation, toroidal, earth-moon thickness) still don't.

## `oriented_trees_in_n_chromatic_digraphs` — flag auto-fixed
The audit flagged a draft using the *dichromatic* number; the disk version uses
`χ([set: underlying D])` — the **ordinary** chromatic number of the underlying graph (Burr's
conjecture), so it is faithful. **done.**

## Reuse + nits
Reused (no restating): `arc`/`induced_digraph`/`del_vertex`/`dgiso`, `outdeg`/`oriented`,
`tournament`/`TT`/`sub_tournament`, `dipath`/`dicycle`, `strongb`, `stable`/`diregular`,
`acyclicb`/`dicolorableb`, `out_branching`/`in_branching`, `oriented_kcolouring`/`dhom`. Nit (review):
the new general digraph primitives (`switched`, `remove_arcs`, `rev_arc`, `contains_subdig`,
`cyclomatic`, `arc_decomp`, …) are not `[@MOVE-to-base]`-tagged — they're a digraph-theory **internal**
layer (base is undirected), so a `digraph-theory` foundations module, not GTBase, is their eventual
home. `indeg` exists in two imported modules → qualified `classic_core.indeg` to avoid the clash.

## Edges
2 candidate: `partitioning_planar_digraphs ⟹ large_acyclic_induced…`, `decomposing_k_arc_strong ⟹
arc_disjoint_out_branching` (recorded `(*@EDGE*)`, not forced).
