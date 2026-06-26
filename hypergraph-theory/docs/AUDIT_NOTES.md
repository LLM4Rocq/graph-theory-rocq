# hypergraph-theory — formalization audit notes

Per-statement decisions (keyed by `formal_name`). **base_ready** run; first milestone in the
`hypergraph-theory` area (namespace `Hypergraph`). Verified: compiles axiom-free, 33/33 grounding
lemmas `Qed`, `check_milestone U12` → ACCEPTED. **Faithfulness: 4/4 OK, 0 flagged.** Leg state:
**4 done, 0 blocked.**

## U12 — hypergraph conjectures
Hypergraphs modelled as vertex-subset families `E : {set {set T}}` — **no mgraph import needed** (the
import-order/line_graph caveat doesn't apply). Sole import `From GTBase Require Export base` (re-exports
all of mathcomp finset/tuple/seq/path/zip). All primitives are genuinely new (Search over base empty).

- `frankls_union_closed_sets` — `union_closed F` (closed under `:|:`).
- `turans_problem_for_hypergraphs` — `k_uniform`, `complete_sub`/`contains_complete` (K_m^{(k)}).
- `are_critical_k_forests_tight` — Berge cycles/acyclicity, `k_forest`/`k_tree`/`critical_k_forest`,
  `hg_connected`.
- `rysers_conjecture` — `r_partite_uniform`, `hg_matching` + `is_matching_number` (ν),
  `hg_cover` + `is_cover_number` (τ); Ryser is τ ≤ (r−1)·ν.

## Edges
None — the four conjectures are independent (no Qed-able relative implication). `implications_U12.v`
is intentionally edge-free (documented in prose, no `(*@EDGE*)` annotations, correctly).

## Nits (cosmetic, no change required)
- `hg_matching` spells out pairwise-disjointness manually; mathcomp's `trivIset` is the idiomatic
  form (`M \subset E /\ trivIset M`). Optional polish.
- `hg_cover` correctly dodges mathcomp's `finset.cover : {set {set T}} -> {set T}` (a different
  notion) via the `hg_` prefix.
- The hypergraph vocabulary here is hypergraph-area-specific; if later phases (e.g. deferred
  hypergraph rows) reuse it, a `hypergraph-theory` foundations module — not base — is the right home
  (base owns *graph* cross-area primitives, not hypergraph ones).
