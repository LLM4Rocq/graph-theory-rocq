# spectral-graph-theory — formalization audit notes

Deferred-tier milestone; first in the `spectral-graph-theory` area (namespace `Spectral`, 11th area).
**base_ready** run. Verified: compiles axiom-free, 12/12 grounding lemmas `Qed`, `check_milestone D5
spectral-graph-theory` → ACCEPTED (5/5 axiom-free). **Faithfulness: 5/5 OK.** Leg state: **5 done.**

## D5 — spectral conjectures (preflighted carrier policy)
**`algC` / `mathcomp.field` is NOT installed**, so the preflight settled a fourcolor-free encoding
(verified): cospectrality via **`char_poly` equality over `int`** (no roots, no field); eigenvalue
magnitude/ordering over an **abstract `(R : rcfType)`** (real-closed field — gives order, `|·|`,
`Num.sqrt`). Import order: `all_boot → sgraph → base → all_algebra perm` (the D1 finding; `perm`
needed for `'S_n`). `foundations/spectral.v` holds `adjmx`/`degmx`/`Lapmx` (L = D−A), `cospectral`,
`determined_by_spectrum` (= `forall H, cospectral G H -> inhabited (G ≃ H)` — ISO, multiset spectrum),
`spectral_radius_le` (rcfType), `is_spectrum` (non-increasing multiset). base UNTOUCHED.

## Per-row
- **`signing…small_magnitude_eigenvalues`** (solved) — over `rcfType`: a symmetric ±1 signing with
  `spectral_radius_le S (2 * Num.sqrt (d-1))`. The `2√(d-1)` bound lives in the rcf.
- **`are_almost_all…determined_by_spectrum`** — asymptotic encoded as an **ε–N limit without reals**:
  `forall m>0, exists N, forall n≥N, m·(total_count n − determined_count n) ≤ total_count n`, i.e.
  the non-determined fraction ≤ 1/m eventually ⇒ determined fraction → 1. Faithful.
- **`does_the_symmetric_chromatic_function_distinguish_trees`** — Stanley's **chromatic symmetric
  function** (combinatorial, NOT spectral): `csf_coeff G k a` = #proper k-colourings with colour-class
  sizes `a`; `same_csf`; distinguish = ∃ non-iso trees with equal CSF. (Disk name reconciled to the
  manifest's canonical truncated formal_name `…distinguish_tr_statement`.)
- **`laplacian_degrees_of_a_graph`** — over `rcfType`: k-th Laplacian eigenvalue ≥ k-th degree
  (Grone–Merris/Brouwer direction), degrees non-increasing.
- **`triangle_free_strongly_regular_graphs`** — ∃ 8 pairwise non-iso triangle-free **primitive** SRGs
  (⟺ one beyond the 7 known). `strongly_regular` got non-triviality guards from correct+ground
  (`connected ∧ 0<k ∧ k<#|G|−1 ∧ regular G k`), excluding the edgeless/disconnected vacuity the audit
  flagged. Reuses base `regular`/`common_nbr`.

## Notes
No edges (the 5 are independent). Nits (review): `strongly_regular` untagged (base candidate if a 2nd
algebraic/spectral area needs it); CSF `proper_colb` is not a redefinition of coloring.v `coloring`
(it tracks colour-class sizes, which needs the `{ffun G -> 'I_k}` encoding).
