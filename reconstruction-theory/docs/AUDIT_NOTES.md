# reconstruction-theory — formalization audit notes

Per-statement decisions (keyed by `formal_name`). **base_ready** run; first milestone in the
`reconstruction-theory` area (namespace `Reconstruction`). Verified: compiles axiom-free, 19/19
grounding lemmas `Qed`, `check_milestone U11` → ACCEPTED. **Faithfulness: 4/4 OK, 0 flagged.**
Leg state: **4 done, 0 blocked.**

## U11 — reconstruction conjectures
All four rows follow the "decks equal up to iso ⟹ graphs iso" idiom, with iso = base's `diso` (`≃`)
wrapped in `inhabited (G ≃ H)` to land in `Prop`. Reused from base verbatim: `diso`, `induced`,
`is_tree`, `E(G)`/`sg_edge_set`, `SGraph`/`sg_sym`/`sg_irrefl`. **mgraph deliberately not imported.**

- `reconstruction` — vertex deck (`vdel_card G v := induced [set u | u != v]`, the card G−v).
- `edge_reconstruction` — edge deck (`del_edge G e`, remove one edge; deck indexed by the edge
  sig-type `{e | e ∈ E(G)}`).
- `switching_reconstruction` — Seidel switching deck (`switch_vertex G v := vertex_switch [set v]`,
  toggle all edges at v).
- `grahams_conjecture_on_tree_reconstruction` — tree reconstruction via iterated `sline_graph`.

## Generic primitives — base candidates (untagged; flagged by review)
`sline_graph : sgraph -> sgraph` (the **simple** line graph — distinct from base's `line_graph :
mgraph -> sgraph`, and *iterable* over sgraph, which base's is not), `del_edge` (single-edge
deletion), `vertex_switch` (Seidel/two-graph switch) are all broadly reusable but kept area-local
**without** `[@MOVE-to-base]` tags. Recommend tagging them; promote when a 2nd area needs them
(`sline_graph` is the likeliest — line graphs recur in colouring / claw-free work).

## Edge
1 candidate: `reconstruction ⟹ edge_reconstruction` (recorded as `(*@EDGE*)`; not Qed-forced —
the classical implication needs a non-trivial counting argument not yet formalized).

## Pitfall (recorded)
`Set Implicit Arguments` makes the leading `(G : sgraph)` of `switch_vertex`/`del_edge`/`vdel_card`
implicit (it occurs in a later argument's type) — apply as `@switch_vertex G v`, etc.
