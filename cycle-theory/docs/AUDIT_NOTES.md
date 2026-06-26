# cycle-theory — formalization audit notes

Per-statement decisions (keyed by `formal_name`). **base_ready** run; first milestone in the
`cycle-theory` area (namespace `Cycle`). Verified: compiles axiom-free, 60/60 grounding lemmas
`Qed`, `check_milestone U6` → ACCEPTED. **Faithfulness: 11/11 OK, 0 flagged.**

## U6 — cycle covers & decompositions

### Carrier + conventions
All 11 rows are undirected-multigraph statements: carrier = coq-graph-theory `mgraph` (= `graph unit
unit`); subgraphs/cycles/matchings/covers are **edge sets** `{set edge G}`, and multisets of cycles
are `seq {set edge G}`. Import order follows the base warning — `From GraphTheory Require Import
mgraph.` **before** `From GTBase Require Import base.` (base only `Import`s mgraph, so U6 imports the
raw edge API itself). Leg state: **11 done, 0 blocked**.

### FIRST SOUND VERIFIED EDGE: `faithful_cycle_covers ⟹ cycle_double_cover`
A real `Qed` reduction (`Theorem faithful_cycle_covers_implies_cycle_double_cover`), and — unlike the
demoted Seymour edge — **both endpoints are faithfully stated** (proper `0<|G|`, `0<|edge G|` guards;
`cdc` = circuits covering each edge exactly twice; `faithful_cover p` = the weighted generalization).
Soundness: instantiate `p := λ_.2`; it is even, and its admissibility (`|cut S| ≥ 2` for every edge
cut) is **exactly bridgelessness**, so `faithful_cover (λ_.2) = cdc`. This is the genuine "Faithful
Cover Conjecture generalizes CDC" fact, not an artifact of a weakened endpoint.

### Candidate edges (honestly not forced)
- `strong_5_cycle_double_cover ⟹ cdc` and `m_n_cycle_covers ⟹ cdc` — **candidate**: member-shape
  mismatch under the committed formulations (strong-5/(5,2)-covers yield *even subgraphs* of fixed
  size, while `cdc` demands *single circuits*). Recorded, not Qed-forced.

### Base-candidate cycle/connectivity vocabulary (promote when a 2nd area needs it)
Flagged cross-area (for flow-/matching-theory later): `mdeg` (multigraph vertex degree `#|edges_at v|`
— the per-vertex companion to base's `mDelta`), `eulerian`, `edge_connected` (k-edge-connectivity),
`mconnected`/`walk_in`/`connected_del_edges`/`connected_del_verts`, `two_connected`, `is_matching`,
`simple_mgraph`. Area-local: `is_circuit`, `cdc`, `faithful_cover`, `admissible`, `cut`,
`cycle_decomposition`/`path_decomposition`, `transition2_system`/`compatible_decomposition`,
`is_eulerian_tour`, `two_factor`, `even_subgraph`, `oddness_le`, `is_bridge`/`bridgeless`, `cubic`.

### Gotcha (recorded)
`count (fun C => e \in C) L` fails carrier inference (`e \in C` unifies `C` with a `predType`);
annotate `fun C : {set edge G} => e \in C`.
