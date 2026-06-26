# packing-theory / U13 — domination audit notes

`check_milestone U13 packing-theory` → ACCEPTED. Axiom-free, 9/9 grounding `Qed`. (U13 spans 3
sub-milestones; this is the packing-theory part.) Reused base `regular`/`k_connected`/`ceil_div` +
coq-graph-theory's `dom.dominating` verbatim; new `is_domination_number` (relational γ, mirroring
U9's `is_min_fvs`/`is_wsat` idiom).

- **`domination_in_cubic_graphs` — done.** `k_connected G 3 -> regular G 3 -> is_domination_number G m
  -> m <= ceil_div #|G| 3` (Reed). Non-triviality genuinely guarded (`k_connected G 3` bakes in
  `3 < #|G|`; K4 witnesses the hypotheses), and γ is well-pinned.
- **`domination_in_plane_triangulations` — BLOCKED (G2).** Abstract `plane_triangulation : sgraph ->
  Prop` placeholder (over-strong/refutable as-written — the standard pre-G2 caveat); graduates when the
  real planarity predicate lands.
