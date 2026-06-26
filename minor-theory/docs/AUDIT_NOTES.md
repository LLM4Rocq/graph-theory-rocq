# minor-theory — formalization audit notes

Per-statement decisions (keyed by `formal_name`). **base_ready** run; first milestone in the
`minor-theory` area (namespace `Minor`). Verified: compiles axiom-free, 9/9 grounding lemmas `Qed`,
`check_milestone U7` → ACCEPTED.

## U7 — minors & immersion

### Library reuse
`minor G H` (G **contains** H as a minor — library order is G-first; every row uses `minor G 'K_n`),
`'K_n` = `complete n`, `k.-connected`, `α`, `χ` from coq-graph-theory; `regular`, `ceil_div` from
base (verbatim). No `mgraph` import (so the directed-line_graph shadowing rule doesn't apply here).

### Leg state: 4 done, 2 BLOCKED (G2)
- **`high_connectivity_no_k_n`, `jorgensens`** — BLOCKED: planarity replaced by an abstract
  `is_planar : sgraph -> Prop` universally quantified at the outermost level (over-strengthening, same
  placeholder pattern as the other planar rows). `apex` and `planar_after_deleting` are built on this
  abstract predicate; they graduate when the real planarity predicate lands at G2.
- **`forcing_k_6_minor`, `seagull`, `coloring_and_immersion`, `forcing_a_2_regular_minor`** — done.

### `forcing_a_2_regular_minor` — guard auto-added (faithful)
The audit flagged a draft missing `0 < #|G|` (on the empty graph the average-degree hypothesis holds
vacuously while no minor exists → the implication would be false). The correct+ground phase had
already inserted `0 < #|G|` before landing, so the disk statement
(`3≤t → 0<#|G| → average_degree_geq G (4t-6) 3 → regular H 2 → #|H|=t → minor G H`) is faithful. **done.**

### Edges
Three **candidate** edges, none forced: `high_connectivity_no_k_n ⇄ jorgensens` (both directions) and
`jorgensens ⟹ forcing_k_6_minor`. Recorded in `implications_U7.v`; not Qed-closed (the planar
endpoints are themselves G2-blocked).

### New cross-area primitives `[@MOVE-to-base]` (promote when a 2nd area needs them)
- `immersion` (G immerses H: injective branch vertices + edge-disjoint branch walks) — colouring ∩
  minor; **base candidate**;
- `path_edges` (edge set of a vertex walk) — immersion helper;
- `average_degree_geq G a b := a·#|G| ≤ b·Σ_v #|N(v)|` (avg degree ≥ a/b, cross-multiplied over ℕ;
  Σ deg = 2|E|) — extremal; **base candidate** (refactor to consume a degree-sum/edge-count helper if
  one is later added to base).
- Area-local, intentionally NOT `[@MOVE-to-base]` until G2: `apex`, `planar_after_deleting` (depend on
  the abstract `is_planar`; cannot migrate until a real `planar` predicate exists).
