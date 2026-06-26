# chromatic-theory / U4 — list-colouring audit notes

Per-statement decisions (keyed by `formal_name`). **base_ready** run; reused base's `Delta`
verbatim. Verified: compiles axiom-free, 28/28 grounding lemmas `Qed`, `check_milestone U4` →
ACCEPTED (11/11 statements axiom-free). U1 in the same package still ACCEPTED.

## List-χ core promoted to base
`list_colourable`, `list_colourable_on`, `choosable`, `is_choice_number` were defined in U4 and
**promoted to `graph-theory-base`** (your ask) — they're the reusable list-colouring vocabulary
for U5 (edge/total via line-graph) and U8 (χ-boundedness). Design choices (all faithful):
- the colour palette is an **arbitrary `finType C`** quantified per use (no fixed colour universe),
  so `choosable G k` ranges over *all* list assignments with lists of size ≥ k;
- `is_choice_number G m` is **relational** (`m` is the least k with k-choosability) to keep the
  statement file proof-free (avoids an `ex_minn` existence obligation).

## Leg state: 10 done, 1 BLOCKED (G2)
- `acyclic_list_colouring_of_planar_graphs_statement` — **BLOCKED**: placeholder planarity
  (`forall is_planar, is_planar G -> …`) is over-strong; real planarity at G2.
- The other 10 rows are faithful + axiom-free (`done`).

## Caveats confirmed
- **`partial_list_coloring` t=0 is fine.** The implications agent annotated it as
  "false-as-formalized (empty-palette/t=0)" and referenced a `…_vacuously_false` lemma — but **no
  such lemma exists** (overclaim). At t=0 the lists are empty and `W := ∅` satisfies
  `list_colourable_on L ∅ ∧ 0 ≤ cl·0`, so the statement is **vacuously true**, not false. Faithful
  for the meaningful regime t≥1; a `1<=t` guard would sharpen it (optional, not required).

## Edges (in `implications_U4.v`, machine-readable `(*@EDGE*)`)
- `partial_list_coloring_0 ⟹ partial_list_coloring` — **candidate** (Albertson–Grossman–Haas);
  not Qed-closed.
- `list_hadwiger ⟹ hadwiger` and `list_total ⟹ behzad` — **refuted-direction** (the §6 demoted
  edges: list-Hadwiger gives only c·t-list-colourability; χ″_ℓ=χ″ doesn't give the Δ+2 bound).
  Cross-milestone targets (Hadwiger is U7, Behzad is U5) — not yet formalized nodes.

## Area-local primitives (base candidates as later milestones need them)
`line_graph` / `total_graph` (mgraph-based) — **U5 (edge/total colouring) will need these → promote
to base when U5 lands**; `mDelta` (multigraph max degree), `complete_multipartite`, `colourable_count`
(λ_L), `paintable` (online choosability), `acyclic_colouring` / `acyclically_choosable`,
`strongly_colorable`. Imports `minor` + `mgraph` from coq-graph-theory directly (outside base's
undirected surface, justified). Nit: British/American spelling mixed (`strongly_colorable` vs the
`…colourable` family) — harmless.
