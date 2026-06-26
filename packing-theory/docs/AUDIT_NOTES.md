# packing-theory — formalization audit notes

Per-statement decisions (keyed by `formal_name`). **base_ready** run; first milestone in the
`packing-theory` area (namespace `Packing`). Verified: compiles axiom-free, 29/29 grounding lemmas
`Qed`, `check_milestone U9` → ACCEPTED. Mixed-carrier file (sgraph **and** mgraph vocabulary in one
file; `mgraph` imported before base).

## U9 — packing, covering, transversals, partitions (13 rows)

### Leg state: 12 done, 1 BLOCKED (G2)
- **`jones`** — BLOCKED: planarity is a universally-quantified abstract `planar : sgraph -> Prop`
  (placeholder, over-strong); real predicate at G2.
- The other 12 rows are faithful + axiom-free.

### `partitioning_edge_connectivity` — directional-walk flag auto-fixed (faithful)
The audit flagged a draft `edge_conn_via` built on coq-graph-theory's `walk` (which only traverses
`source → target`, so over the directed `graph unit unit` carrier it encoded *directed* a-edge-
connectivity — an undirected-connected graph with one "wrongly oriented" edge would fail it). The
correct+ground phase had already replaced `walk` with a **local undirected `uwalk`** (traverses
`source→target` OR `target→source`), so the disk statement is faithful undirected edge-connectivity.
**done.** ⚠️ Follow-up: this surfaces that **cycle-theory/U6**'s connectivity (`mconnected`,
`connected_del_edges`, …) is built on the library's directional `walk` and may carry the same latent
directed/undirected defect — worth re-checking when the connectivity layer is promoted.

### Edges
1 candidate: `triangle_packing_vs_triangle_edge_transversal ⟹ jones` (recorded as `(*@EDGE*)`; not
Qed-forced — jones is G2-blocked anyway).

### Base-promotion candidates (PENDING your review — not yet promoted)
Per the agreed gate-promotion-on-review policy, U9 keeps everything local; these are the cross-area
primitives to decide on:
- **`k_connected`** — defined in **hamiltonicity/U2, homomorphism/U3, packing/U9** (3 areas). U9 uses
  the Whitney separator-free form; definitions across areas must be reconciled before promoting one
  canonical base version.
- **`triangle_free`** (U3, U9), **`is_matching`** (U6 *mgraph* vs U9 *sgraph* — carrier differs),
  **`hamiltonian_cycle`/`is_hamiltonian`** (U2, U9), and **`uwalk`** (undirected-walk primitive; if
  promoted, U6's connectivity should be retargeted onto it to fix the directional-walk issue above).

### Area-local primitives (this milestone)
`is_P3`, `is_triangle`/`tri_edges`/triangle-packing/-transversal, `friendly_partition`,
`all_but_finitely_many_regular`, `pack` (graph packing), `is_induced_path`, `hits_all_cycles`/
`is_min_fvs`, `cycle_packing`, `del_bipartite`, `matching_cut`/`avg_deg_lt`, edge-disjoint Steiner
trees, `hypercube`/matching-extension, weak-saturation, `cut_mg`/`is_tjoin`/T-cut/`graft`.

### Gotchas (recorded)
`[/\ … ]` supports ≤ 5 conjuncts (`and5`); `count (fun X : {set edge G} => e \in X) s` needs the
explicit binder annotation; sgraph defs with a later `seq G` arg make the sgraph implicit — use
`Arguments … : clear implicits` (the U2 idiom).
