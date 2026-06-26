# graph-theory-misc — formalization audit notes

Per-statement decisions (keyed by `formal_name`). **base_ready** run; first milestone in the
`graph-theory-misc` area (namespace `GTMisc`); the catch-all for OPG rows without a dedicated area.
One of three U13 sub-milestones. Verified: compiles axiom-free, 32/32 grounding lemmas `Qed`,
`check_milestone U13 graph-theory-misc` → ACCEPTED. **Leg state: 12 done, 0 blocked.**

## U13 (graph-theory-misc) — 12 diverse rows
Reused from base verbatim: `cartesian_product` (pebbling), `subdivision` (book-thickness;
`subdivide1 = subdivision G 2`), `regular`, `girth_geq`, `ball` (diameter/girth), `is_hom` (subgraph).

## Two flags — both auto-fixed by correct+ground (verified on disk)
- **`is_tree` name-clash → fixed.** The draft redefined `is_tree` (shadowing base's re-exported
  `is_tree : {set G} -> Prop`). On disk it is renamed **`is_tree_card`** (`connected [set:G] ∧
  n_edges G = #|G|−1`), so no base name is shadowed. (graceful-tree + gold-grabbing use `is_tree_card`.)
- **`a_gold_grabbing_game` base-case bug → fixed.** The audit flagged `is_leaf` using `== 1` (exactly
  one neighbour), which wrongly excluded the final/isolated vertex and mis-computed the Bellman value.
  Disk version uses **`#|N(v) :&: S| <= 1`**, so the terminal single vertex is a leaf and the game value
  recursion is correct. **done.**

## Cross-area base candidates (PENDING review — kept local per gate-promotion-on-review policy)
- **`degenerate` / k-degeneracy** — now appears here **and** in topological-graph-theory/U13
  (`k_degenerate`) → 2 areas; a promotion candidate (reconcile the two forms first).
- **`avgdeg_geq`** (average degree, fraction-free `d·|V| ≤ 2|E|`) overlaps with minor-theory/U7's
  `average_degree_geq` → candidate.
- `has_diameter` / `has_girth` (general metric invariants), `oedges`/`n_edges` (oriented-edge count)
  are plausibly reusable too. Will surface these in the next promotion review.

## Edge
1 candidate from `bene_conjecture_graph_theoretic_form_0` (recorded `(*@EDGE*)`; not forced).

## Area-local (this milestone)
`induced_cycle`, `is_max_clique`/`splits_max_cliques`, `book_embedding`/`is_book_thickness`,
multistage/`rearrangeable`/`se_adj` (shuffle-exchange + Beneš), `pebble_move`/`is_pebbling_number`,
`graceful_labeling`, `imb`/`graphic` (imbalance), `gold_total`/`leaf_game_solution`,
`hexagonal`/`weighted_chromatic_number`.
