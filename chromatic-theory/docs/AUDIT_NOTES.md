# chromatic-theory — formalization audit notes

Per-statement formalization decisions that a faithfulness reviewer should know (the things
*not* obvious from the Rocq text alone). Keyed by `formal_name`. Provenance: produced by the
`area-milestone-pipeline` QA workflow, landed in commit `13cd1ad` (pre-G3 first cut).

## U1 — chromatic-number bounds

### `cycles_in_graphs_of_large_chromatic_number_statement` — the `2 < k` floor (CONFIRMED faithful)
The OPG statement ("if χ(G)>k then G has ≥ (k+1)(k−1)!/2 cycles of length 0 mod k") is
**necessarily about k ≥ 3**, and the node encodes exactly that (`2 < k`):
- The conjecture's *own* extremal/tightness example is **K_{k+1}**, which has exactly
  (k+1)(k−1)!/2 cycles of length **k** — but length-k cycles are genuine cycles only for
  **k ≥ 3**. At k=1, K₂ has 0 cycles (formula says 1); at k=2, K₃ has 0 *even* cycles
  (formula says 1.5). So the unrestricted `forall k` statement is **false** at k=1 (witness
  K₂) and k=2 (witness C₅/K₃) — these are genuine counterexamples, not encoding artefacts.
- The one *proven* instance is k=3 (Chudnovsky–Plumettaz–Scott–Seymour; simpler proof
  Wrochna; the count generalisation is Brewster–McGuinness–Moore–Noel), confirming the
  meaningful regime starts at k=3.
- Encoding also uses a `2 < L` filter on `count_cycles_mod` so a single edge (a "length-2
  closed walk") is never miscounted as a cycle. For k ≥ 3 the relevant lengths are L ∈
  {k, 2k, …} ≥ 3, so `2 < L` holds automatically.
- **Decision:** faithful. The `2 < k` guard is the minimal restriction making the statement
  match its own tightness example and the literature; documented in the source comment too.

### `erdos_faber_lovasz_statement` — status `solved`
SOLVED for all large n (Kang–Kelly–Kühn–Methuku–Osthus, 2023). Per the statement-only policy
it is still a `Definition _statement`; a proof would be optional `applications/` work and is
out of M-CORE scope.

### `reeds_omega_delta_and_chi_statement` ⊥ `the_borodin_kostochka_statement` — independence
No implication edge between Reed and Borodin–Kostochka in **either** direction: both sandwich
χ in [ω, Δ+1] but neither implies the other (refuting instance Δ=9, ω=8 → χ=9 satisfies Reed,
violates B-K). `implications_U1.v` records both directions as `refuted-direction`; **no false
edge was forced through**.

### Pre-G3 primitive ownership
`U1.v` defines cross-area primitives tagged `[@MOVE-to-base]` — `Delta` (Δ), `common_nbr`,
`regular`, `girth_geq`, `ceil_div` — pending `graph-theory-base` (gate G3). When `base/`
lands, these move there and `U1.v`'s imports retarget from `coq-graph-theory` to `base/`.
Area-specific primitives (`double_critical`, `zero_two_graph`, `n_cycles_len`,
`count_cycles_mod`, `edge_disjoint_clique_union`, `graph_power`, `subdivision`, `frac_power`,
`valency_variety`) stay in `chromatic-theory`.
