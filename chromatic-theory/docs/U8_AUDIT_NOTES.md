# chromatic-theory / U8 — χ-boundedness audit notes

Per-statement decisions (keyed by `formal_name`). **base_ready** run; 3rd chromatic milestone
(joins U1/U4/U5 in the package). Verified: compiles axiom-free, 16/16 grounding lemmas `Qed`,
`check_milestone U8` → ACCEPTED. **Faithfulness: 3/3 OK, 0 flagged.** Leg state: **3 done, 0 blocked.**

## Base reuse
χ/`chi_mem`, ω/`omega_mem`, `Delta`, `ceil_div`, `induced`, **`is_tree`** (= `is_forest ∧ connected`,
satisfies the forbidden-tree row with no local redefinition), `≃`/`diso` — all reused verbatim from
base. No cross-area primitive redefined.

## New χ-boundedness vocabulary (chromatic-local, `chi_bounded` is a `[@MOVE-to-base]` candidate)
- `chi_bounded F := exists f : nat -> nat, forall G, F G -> χ([set: G]) <= f (ω([set: G]))` — the
  binding-function definition. Both consumers (forbidden-tree, vertex-minor rows) are inside
  Chromatic, so it stays local per the migration policy; promote when a non-Chromatic area needs it.
  Nit (not a defect): `f` is not required monotone — this is the standard textbook χ-bounded
  definition (a binding function may always be taken nondecreasing, so it's equivalent).
- `has_induced T G := exists S, inhabited (T ≃ induced S)` — induced-subgraph containment (base's
  `induced` + `diso` wrapped in `inhabited` to land in `Prop`).
- `local_complement G v` — an sgraph via `lc_rel x y := (x != y) && ((x -- y) (+) ((x--v)&&(y--v)))`
  (toggles adjacency among distinct common neighbours of `v`; symmetric + irreflexive proved).
- `vminorR` / `vertex_minor` — inductive vertex-minor relation (refl / local-complementation step /
  vertex-deletion step, each up to `≃`); `vminor_closed`, `proper_class` for Row 3's hypotheses.

## Edge
- `vertex_minor_closed_classes_are_chi_bounded ⟹ graphs_with_a_forbidden_induced_tree_are_chi_bounded`
  — **candidate** (recorded as a `(*@EDGE*)` annotation; not Qed-forced). The U7 template hardening
  held: the agent emitted the machine-readable annotation, not just prose.
