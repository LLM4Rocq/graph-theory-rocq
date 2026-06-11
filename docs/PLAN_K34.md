# Formalization plan: Conjecture 5.10 at k = 3 and k = 4 (the unified family)

**Target.** Formalize `conjecture_5_10_k345_unified.md` of the
`tournament_clique_number_omega_cluster` project for the two cases not yet
in the library:

> For every odd n = 2m+1 ≥ 7: **ACₙ is 3-ω̄-critical** and **ACₙ[C₃] is
> 4-ω̄-critical** — each an infinite family, so Conjecture 5.10 of
> Aboulker–Aubian–Charbit–Lopes holds at k = 3 and k = 4, and Question 5.9
> fails there.

Combined with the k = 5 theorem already formalized (M0–M6), the headline
becomes the unified statement: **for every k ∈ {3,4,5} there are
infinitely many k-ω̄-critical tournaments.**

**Status:** v1.1 (2026-06-11) — decisions D13–D15 RESOLVED (recommended
options, Marc's sign-off). Milestones **M13–M17**, same repository.

**Standing principle (D12, Marc's instruction): generality first.** Every
new statement at the most general level at which it is true; shared
machinery factored where both k = 4 and k = 5 (and future constructions)
can use it.

---

## 1. What is already formalized (the big surprise: k = 3 is DONE)

- **k = 3 is fully proved** since M4: `omegabar_AC` (ω̄(ACₙ) = 3, with H8 as
  `autocorr_lo`/`autocorr2` + `domnum_AC_ge3`), `omegabar_AC_del`
  (ω̄(ACₙ−v) = 2 ∀v), **`AC_kcritical3`**, `AC_vertex_transitive`,
  `card_AC` (#|ACₙ| = n). What is missing is ONLY the Conjecture-5.10 /
  Question-5.9 **packaging** (the analogues of `conjecture_5_10_at_k5`,
  `question_5_9_fails_at_k5`) — a few dozen lines.
- **k = 5 is fully proved** (M0–M6), including the packaging.
- Reusable for k = 4 with no new work:
  - `omegabar_lexprod_ge` (substitution lower bound) → ω̄(ACₙ[C₃]) ≥ 3+2−1;
  - `omegabar_embed` + the constant-h copy t ↦ (t,1) → deletion lower
    bound ≥ 3 (even simpler than k5's embedding: the doc's "a constant-h
    copy is a full ACₙ");
  - `omegabar_C3` = 2, `card_C3` = 3; `lexprod` + `card_lexprod`;
  - `lexprod_vertex_transitive` (added in M6) + `vt_kcritical` +
    `omegabar_del_vt`;
  - the ACₙ arc-fact kit (`acn_arc_facts.v`: `AC_arc_lt`/`AC_arc_gt` gap
    characterizations = the doc's four arc-facts table, `AC_mem_Hi/Lo`,
    val-arithmetic) and `bucket_bound`;
  - the k5 band machinery (`band`, `band1P/2P/3P`, `AC_wrapF` "no backedge
    within a monotone m-interval", `band_gap`) — currently buried in
    `applications/k5/cells.v`, wanted by k = 4 too (→ D13);
  - the `realize`/`ltp_realizeE` order-realization workhorse and the
    k5 file architecture (key order as a radix nat, occupancy counting).

**The genuinely new mathematics to formalize — k = 4 only:**
1. ω̄(ACₙ[C₃]) ≤ 4 — the merged order ≺* casework
   (`proof_omega_AC_n_C3.md`);
2. ω̄(ACₙ[C₃] − (0,0)) ≤ 3 — the `d_then_c` order: five bands, the
   (3,1)-exclusion s-split, and the (2,2)-lemma with the core
   incompatibility ¬(1+δ ∈ g ∧ m+1+δ ∈ g)
   (`proof_deletion_AC_n_C3.md`);
3. `C3_vertex_transitive` (translation x ↦ x+t on 'Z_3; C3's arc is
   `v == u+1`, so this is the cayley-translation argument in miniature).

Both k = 4 documents are marked red-team-passed with every arc-fact
machine-checked uniformly in m; conventions match ours (same g, same
bands) — the dossier still re-derives everything in val-arithmetic form.

## 2. New general library material (D12 dividends)

- **`kcritical_proper_sub`** (in `invariants/critical.v`): for ANY
  tournament, `kcritical k T -> S != setT -> ω̄(sub_tournament S) ≤ k−1`
  (proper sub omits a vertex; embed into the deletion; monotonicity).
  This is the Question-5.9-failure mechanism stated ONCE; the k=3, k=4
  packagings use it, and k5's `proper_sub_omegabar_le4` becomes its
  instance (k5 files left untouched; the general lemma added beside).
- **`card_clique_classes`** (general partition counting, in
  `invariants/omegabar.v` or prelude): for any finite K and
  `f : V -> nat` with values < b: `#|K| = Σ_(i < b) #|[set u in K | f u == i]|`.
  k5's `card_clique_cidx` and the k4 key-class/band counts are instances;
  new constructions get it for free.
- **Band kit relocation (D13):** move `band`, `band1P/2P/3P`, `AC_wrapF`,
  `band_gap` from `applications/k5/cells.v` to a new shared
  `applications/acn_bands.v` (imported by k5/cells.v — statements
  unchanged, mechanical cut; full k5 regression run afterwards).
- `C3_vertex_transitive` placed with the other vt facts
  (`constructions/circulant.v`, which already imports automorphism +
  tournament).

## 3. Milestones

- **M13 — Dossier + oracle.** `docs/k34_dossier.md`: re-derive both k = 4
  caseworks in our val-arithmetic conventions with item IDs
  (V-* for the value bound: classes K2..K5, caps (1,2,2,1), the two
  cross-class cases; D-* for the deletion bound: bands B1..B5, the
  (3,1) s-split, the (2,2)-lemma with its B1/B2 cross analysis and B3
  sub-case, the core incompatibility); pin the order definitions as
  radix keys (≺*: key (c t + d h, t, h); `d_then_c`: key (d h, c t, t, h))
  realized via `realize`. Oracle: extend `scripts/` with AC[C3]
  construction + checks (ω̄ = 4, deletion = 3 for small n; the class caps;
  the (2,2) incompatibility for a range of m; the (3,1) s-split).
  *Exit: dossier reviewed, oracle green, D13–D15 signed off.*
- **M14 — General additions + cheap k3/k4 facts.**
  `kcritical_proper_sub`, `card_clique_classes`, the acn_bands relocation
  (+ full k5 regression), `C3_vertex_transitive`;
  `applications/k4/k4_lower.v`: ω̄(ACₙ[C₃]) ≥ 4 and
  ω̄(ACₙ[C₃]−(0,0)) ≥ 3 (constant-h embedding). *Exit: all axiom-free,
  k5 build untouched-green.*
- **M15 — The value bound.** `applications/k4/k4_value.v`:
  ω̄(ACₙ[C₃]) ≤ 4 via ≺*. Within-class caps (K5: singleton; K2: forward;
  K4: chain + the two (m,0)-backedges; K3: bipartite low/high), then the
  two cross-class cases (s₄ = 2 with the forced (m,0); s₄ ≤ 1 with the
  forced profile (1,1,2,1) refuted by the forward arc (m+1)→1).
  *Exit: `omegabar_T4 : ω̄(ACₙ[C₃]) = 4` (with M14's ≥). Budget: ≈ ⅓ of
  k5's obstructions.v.*
- **M16 — The deletion bound (the crux).** `applications/k4/k4_del.v`:
  ω̄(ACₙ[C₃]−(0,0)) ≤ 3 via `d_then_c`. Items: per-band no-backedge
  (AC_wrapF), the (3,1)-exclusion (s-split into [1,m−1]∪{m+1}, {m},
  [m+2,2m]), the (2,2)-lemma (X's blocks, B1/B2 internal forward, the
  cross-B1–B2 reduction to b₁ = 1 ∧ b₂ = m+1, the **core incompatibility**
  ¬(1+δ ∈ g ∧ m+1+δ ∈ g), and the B3 sub-case with s' = m forced).
  *Exit: `omegabar_T4del : ω̄(ACₙ[C₃]−v) = 3` for all v (via vt).
  Budget: ≈ ½ obstructions.v.*
- **M17 — Mains + the unified theorem + wrap-up.**
  `applications/k4/k4_main.v`: `T4_kcritical4`, `card_T4` (= 3n),
  `conjecture_5_10_at_k4`, `question_5_9_fails_at_k4`.
  `applications/unified.v`: k = 3 packaging (`conjecture_5_10_at_k3`,
  `question_5_9_fails_at_k3` from `AC_kcritical3` + `kcritical_proper_sub`)
  and the headline
  `Theorem conjecture_5_10_at_345 : forall k, 3 <= k <= 5 ->
   forall N, exists T : tournament, kcritical k T /\ N < #|T|.`
  Axiom audit (every new exit), CHANGELOG/README/plan updates, CI green,
  memory. *Done.*

## 4. Decisions needing sign-off

- **D13 — band kit relocation. ✅ RESOLVED:** move the five band lemmas
  out of `k5/cells.v` into shared `applications/acn_bands.v` so k4 and
  future ACₙ constructions reuse them (k5 imports it; full regression).
  Fallback (zero-risk): k4 files import `k5/cells.v` directly — works but
  couples k4 to the k5 application.
- **D14 — order realization style for k4. ✅ RESOLVED:** same as k5
  cells.v — encode each order as a radix nat key and `realize` it
  (`≺*`: (c t + d h)·3n + t·3 + h; `d_then_c`: ((d h)·3 + c t)·3n + t·3 + h
  — exact radix fixed in the dossier), with `find`-free direct class
  predicates. Proven pattern, no new machinery.
- **D15 — headline statement form. ✅ RESOLVED:** per-k theorems plus
  the quantified `conjecture_5_10_at_345` (k ranged over 3 ≤ k ≤ 5 by
  case analysis); Question 5.9 failures stated per-k in the k5 style
  (witness family + only-subtournament-is-T-itself), all derived through
  the general `kcritical_proper_sub`.

## 5. Risks

1. The (2,2)-lemma's B3 sub-case and the (3,1) s-split are the fiddly
   residue-arithmetic spots (the doc's own review flagged and repaired
   them) — the dossier re-derives them in val-arithmetic *before* any
   Rocq, with the k5 lessons applied (never rewrite under 'Z_n indices;
   generalize vals first).
2. The acn_bands relocation touches k5 files — mitigated by mechanical
   cut-paste and a full-build regression in the same commit.
3. The merged-order key mixes c+d sums — off-by-one in the radix encoding
   would surface late; the dossier fixes the exact nat encodings and the
   oracle checks key monotonicity on small instances.

## 6. What this buys the library

`kcritical_proper_sub` and `card_clique_classes` are general tournament
tools; the shared band kit makes ACₙ-based constructions a reusable
platform (three applications already: k3, k4, k5); and the repo will
contain the complete formal verification of the unified note — all three
families, one architecture, every k ∈ {3,4,5} of Conjecture 5.10 that is
humanly known.
