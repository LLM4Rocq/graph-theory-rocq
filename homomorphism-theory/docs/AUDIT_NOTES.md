# homomorphism-theory — formalization audit notes

Per-statement decisions (keyed by `formal_name`). **base_ready** run: `From GTBase Require Import base`,
reusing base's `tensor_product`, `is_hom`/`homs_to`, `is_core`, `regular`, `common_nbr`, `girth_geq`
**verbatim** (no redefinition — the hardened base paying off). Verified: compiles axiom-free, 36/36
grounding lemmas `Qed`, `check_milestone U3` → ACCEPTED 9/9.

## U3 — homomorphisms, cores, products

### Leg state: 9 done, 1 BLOCKED (G2)
- **`mapping_planar_graphs_to_odd_cycles_statement` — BLOCKED.** Same placeholder-planarity defect
  as U2's planar rows: `forall (is_planar : sgraph -> Prop), …` drops planarity, reducing to
  `forall G k, 0<k -> girth_geq G (4k) -> homs_to G (C_{2k+1})`, which is *strictly stronger* than
  the conjecture (asserts the hom for non-planar G too). Real planarity predicate at G2.
- The other 9 rows are faithful + axiom-free (`done`).

### `hedetniemis_statement` — status `disproved`, reuses base `tensor_product`
Hedetniemi `χ(G × H) = min(χ G, χ H)` is **DISPROVED** (Shitov, 2019). Stated as a `Definition`
(statement-only policy) over **base's `tensor_product` (×)** — the key reuse test for the hardened
base; it did NOT redefine the product. A refutation is optional `applications/` work, out of M-CORE.

### `pentagon` → `weak_pentagon`
Recorded as a **candidate** edge (Nešetřil) in `implications_U3.v`, **not** proved/forced (needs the
exact endpoint formulations first; the Qed gate decides). No false edge asserted.

### New cross-area primitives — migration triggers
- **`graph_power` / `subdivision` / `frac_power`** are now defined in **both** chromatic-theory/U1
  **and** homomorphism-theory/U3 → **2nd-area trigger: promote this family to `base/`** (same as
  `cartesian_product` was), then retarget U1 + U3. (Tagged `[@MOVE-to-base]` here.)
- `k_connected` also appears in U2 + U3 → base candidate.
- Area-specific (stay local): `cycle_graph`/`C5`, `path_graph`, `star_graph`, `longest_cycle`/`chord`,
  `pcayley` (Cayley of the power group Mᵏ), `hom_equiv`, `strongly_regular`/`srg`, `is_path`/`longest_path`,
  `hom_ffun`/`endo_count`, `triangle_free`/`bipartite_rel`.

### Toolchain notes
- **Cayley row workaround:** in mathcomp 2.x (HB), `{ffun 'I_k -> M}` exposes no directly-nameable
  `finGroupType` (`[finGroupType of …]` is gone). Resolved by quantifying the connection set as
  `S : {set {ffun 'I_k -> M}}` and using `M`'s group ops pointwise (`pdiff f g := [ffun i => f i * (g i)^-1]`) —
  a faithful Cayley graph of Mᵏ needing only `M : finGroupType`. Needs `From mathcomp Require Import fingroup`
  (carries no graph vocabulary; no overlap with base).
- Nit: `hom_ffun` re-implements `is_hom` as a **boolean** `[forall x,forall y, (x--y) ==> (f x -- f y)]`
  over `{ffun G->G}` (justified — `#|set|`-counting endomorphisms needs a decidable predicate).
