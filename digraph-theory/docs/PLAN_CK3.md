# Formalization plan: Cheng–Keevash Conjecture 1 at δ = 3

**Target.** A formal, axiom-free Rocq/MathComp proof of
`problems/directed_path_minimum_outdegree/docs/k3_hand_proof.md`:

> Every oriented graph D with δ⁺(D) ≥ 3 contains a directed simple path of
> length 6.

This closes the δ = 3 case of Cheng–Keevash Conjecture 1 (Thomassé's path
conjecture, oriented version) and strengthens their Theorem 4 (ℓ ≥ 5) to
ℓ ≥ 6 = 2δ at δ = 3.

**Status:** v1.1 (2026-06-11) — decisions D8–D11 RESOLVED (recommended
options, Marc's sign-off), with one overriding design principle added:

> **D12 — generality first.** Every statement is made at the most general
> level at which it is true, so the library is reusable by others: the
> dipath layer, ℓ(D), the surgery kit, Lemma A/D, strong connectivity, the
> sink-SCC reduction and the cut-crossing lemma are stated for arbitrary
> `diGraphType` (no orientedness, no degree hypotheses); the average bound
> and out-selection for any oriented graph / any k; the Lemma 7 kernel
> uniform in δ. δ = 3 enters only in `applications/ck3/{endgame,main}.v`,
> and hypotheses are taken per-lemma (not baked into section-wide
> assumptions when a lemma needs less).

**Host:** this repository (`digraph-theory`), continuing the milestone
series at **M7–M12**. The proof grows the reusable library exactly where it
is thinnest (oriented graphs, directed paths, strong connectivity) and adds
a second marquee application beside `applications/k5/`.

---

## 1. Source material and its trust status

- `k3_hand_proof.md` — the proof to formalize. Audited in
  `CORRECTNESS_REVIEW_2026_05_18.md` (verdict: *correct*, cross-checked
  line-by-line against the paper PDF).
- Cheng–Keevash, *A note on long directed paths in digraphs with large
  minimum outdegree*, arXiv:2402.16776v4 / SIDMA 38(4). The hand proof uses
  **Lemma 7's statement AND its proof internals**: the construction
  S = B⁻, Claim 10 (no two disjoint long cycles), Claim 11
  (N⁺(v_{a−1}) ⊆ V(P)), Claim 12 (N⁺(B⁻) ⊆ V(C)), the count
  |C| ≥ |S| + δ − δ⁺(S), and the a ≠ 0 step. §4 of the paper (≈ 60 lines
  of LaTeX, fetched and read) contains all of them; they must be
  re-proved formally, not cited.
- Known landmine (flagged in the review): the paper's closing line proves
  δ⁺(S) ≥ 2δ+1−ℓ with |P| silently meaning the *vertex* count. With the
  arc-length convention the safe headline is δ⁺(S) ≥ 2δ−ℓ. We use only the
  safe bound; if the +1 falls out of our formal count, record it as a
  bonus corollary.
- Python oracle: `scripts/` of the problem directory already computes
  longest paths (`verify_directed_path_counterexample.py`) — base for
  per-claim oracles (§5).

## 2. The proof, reorganized for formalization

The hand proof factors cleanly into a **general kernel** (all of
Cheng–Keevash Lemma 7, uniform in δ) and a **δ = 3 endgame** (Steps 4–8,
finite reasoning about ≤ 6 named vertices). The kernel internals never use
δ = 3, so we formalize **Lemma 7 in full generality** and get for free:

- the δ = 2 case of Conjecture 1 (|S| ≤ 2 forces δ⁺(S) = 0 — 5 lines);
- the oriented half of Cheng–Keevash **Theorem 4**: ℓ(D) ≥ ⌈1.5δ⌉
  (plug the oriented average bound into the kernel — 10 lines);
- the citable library theorem `lemma7` for any future δ = 4 work.

Important consequence: **we never need Theorem 4 as a prerequisite.** The
hand proof invokes it (ℓ ≥ 5) only to put a length-5 path in hand; formally
we instead run the kernel on a longest path of length ℓ ≤ 5 and the
degenerate cases ℓ ≤ 4 die immediately (δ⁺(S) ≥ 2δ−ℓ ≥ 2 against the
average bound on |S| ≤ 3 vertices). One section, no external input.

Statement conventions to pin in M7 (the dossier):

- ℓ(D) = number of **arcs** of a longest simple directed path;
- the final theorem needs `0 < #|D|` (for the empty graph the δ⁺
  hypothesis is vacuous but there is no path); with one vertex present,
  δ⁺ ≥ 3 already forces #|D| ≥ 7 via the average bound;
- "oriented" = irreflexive + no antiparallel pair (`arc u v -> ~~ arc v u`
  subsumes irreflexivity… it does not: take u = v — keep both).

## 3. New library modules (the gap analysis)

What exists after M0–M6: `diGraphType`/`tournament` HB hierarchy,
sub-digraphs on `{x | P x}`, `N_out`/degree counting on tournaments,
`{perm T}` orders, ω̄ machinery. What is missing, by module:

1. **`core/oriented.v`** — HB structure `Oriented` between `DiGraph` and
   `Tournament` (mixin: `arc_antisym : forall u v, u --> v -> ~~ (v --> u)`
   + irreflexivity). Tournaments satisfy it (totality is a xor) — provide
   the factory/instance so every tournament is an oriented graph. Out-degree
   `outdeg v = #|N_out v|` generalized to digraph level; δ⁺ as a bigmin or
   `[forall v, k <= outdeg v]` predicate. The **handshake/average bound**:
   in an oriented graph, Σ_v outdeg v = #arcs ≤ binom(n, 2), hence
   `min outdeg ≤ (n−1)/2` (used three times: n ≥ 2δ+1, kill |S| ∈ {1,2},
   cap δ⁺(S) = 1). The **k-out-selection**: if δ⁺(D) ≥ k there is a
   spanning sub-relation with outdeg exactly k (choose a k-subset of each
   N_out; gives a `RelDigraph` instance, oriented, whose paths are paths
   of D).
2. **`core/dipath.v`** — directed simple paths and ℓ(D). See D8: reuse
   GraphTheory's `pathp`/`upath` layer (already a dependency, built on
   MathComp `path`) through a projection of our `diGraphType` onto their
   `diGraph` relType — the same pattern as the existing `to_GT` for
   sgraphs. On top: `ell D` (max arc-length of a simple path, via tuples
   of vertices as the finType of candidate paths + `arg max`), monotone
   under sub-digraphs/arc-deletion, **Lemma A** (out-neighbours of the
   last vertex of a maximum path lie on it), **Lemma D** (the endpoint
   cycle C = v_a…v_ℓ v_a from the minimum back-arc, |C| = ℓ−a+1 ≥ δ+1),
   and the **surgery kit**: cycle-minus-one-arc = path, unroll a cycle
   from any vertex, concatenate vertex-disjoint paths, extract a cycle
   from a path plus a back-arc. This kit is what Claims 10–12 consume.
3. **`invariants/strong.v`** — strong connectivity via fingraph's
   `connect`: `strongb D`, the **sink-SCC trick** (the reachable set R(x)
   of an x minimizing |R(x)| is closed under arcs and strongly connected —
   no general SCC theory needed), out-degrees survive inside a sink SCC,
   and the **cut-crossing lemma** (strong + ∅ ≠ A ⊊ V ⟹ an arc from
   V∖A into A). Composes into the reduction R1–R3 of the hand proof:
   from oriented D, δ⁺ ≥ 3 ⟹ a strong, 3-outregular, oriented H with
   ℓ(H) ≤ ℓ(D) and #|H| ≥ 7.
4. **`applications/ck3/lemma7.v`** — the kernel (§4 of the paper), one
   section: D strong, outdeg ≡ δ, oriented, n ≥ 2δ+1, P a longest path
   (ℓ < 2δ) chosen with **maximum cycle bound** (arg max over the finType
   of (ℓ+1)-tuples that are simple paths — the choice the hand proof's
   Step 2 makes). Contents: Claim 10, a ≥ 1, Claim 11 (the hard one:
   maximal path in the complement induced subgraph + farthest-out-neighbour
   cycle + Claim 10), Claim 12 (uses the cycle-bound-maximal choice),
   |B⁻| = |B| (predecessor-in-C bijection), the count
   |C| ≥ |S| + δ − δ⁺(S), and the exit `lemma7`: ℓ(D) < 2δ ⟹ exists
   S ⊆ V, |S| ≤ δ, δ⁺(induced S) ≥ 2δ − ℓ(D). Corollaries:
   `ck_theorem4_oriented` (ℓ ≥ ⌈1.5δ⌉), `ck_conj1_delta2`.
5. **`applications/ck3/endgame.v` + `main.v`** — Steps 4–8 at δ = 3:
   |S| = 3 and a = 1 forced; S is a directed triangle with v₅ ∈ S; each
   s ∈ S beats both vertices of V(C)∖S (count 3 − 1 = 2 = |V(C)∖S|); the
   five antiparallel implications (P1)–(P4),(C1); σ-closure: S is invariant
   under the 5-cycle predecessor permutation on V(C), hence S ∈ {∅, V(C)}
   — contradiction with |S| = 3 ∋ v₅. Main theorem:
   `Theorem ck_conj1_delta3 (D : oriented) : 0 < #|D| ->
    (forall v, 3 <= outdeg v) -> 6 <= ell D.`
   (σ-closure is finite: S ranges over subsets of the 5 named vertices —
   direct case analysis, far smaller than k5's obstructions.)

## 4. Milestones

- **M7 — Dossier + oracle. ✅ Done (2026-06-11).** Delivered:
  `docs/ck3_dossier.md` (items O1–O2, S1–S2, R, M-ℓ, K-A/Ext/D/a1/10/11/
  AB/B⁻/12/count, K-7, T4, C2, E0–E5, MAIN; landmines 1–5 resolved —
  including a NEW one found by the oracle: paper Claim 6 is false as
  stated, ℓ(D_{1,2}) = 2δ+1 not 2δ; unused in our chain), K-12 upgraded
  to an any-digraph statement, `paper/ck3_excerpts.md`,
  `scripts/ck3_oracle.py` + `test_ck3_oracle.py` (52 tests green).
  Original scope: Expand `k3_hand_proof.md` into a
  self-contained dossier (`docs/ck3_dossier.md` here): every claim of §3–§4
  of the paper restated and re-proved with our arc-length conventions and
  named vertices, the two known landmines resolved on paper (the |P|
  vertex/arc count; the δ+1 vs δ+2 slack in Claim 11's cycle C₁), the
  exact statement list of §3 above frozen. Vendor the paper's §4 into
  `paper/` (alongside k5_theorem.tex). Extend the Python oracle: random
  strong 3-outregular oriented graphs; check Lemma A, Claims 10–12, the
  count, lemma7's conclusion, and the final theorem on all n ≤ 9 instances
  the sampler reaches. *Exit: dossier reviewed; oracle green; D8–D11
  signed off.*
- **M8 — Oriented + degrees. ✅ Done (2026-06-11).** `core/oriented.v` (§3.1). *Exit:*
  `oriented_avg_bound`, `outregular_reduction`, tournament-is-oriented
  instance; axiom-free; oracle cross-check of the average bound.
- **M9 — Dipaths + ℓ. ✅ Done (2026-06-11)** (D8 fallback exercised: own seq layer over MathComp path/cycle — graph-theory's pathp/upath layer sits below extremal-path surgery needs). `core/dipath.v` (§3.2). *Exit:* `ell` API
  (monotonicity, witness), `lemma_A`, `endpoint_cycle`, surgery kit
  lemmas, all oracle-checked on C3/TT_n/AC_n (ℓ(TTₙ) = n−1,
  ℓ(C3) = 2, ℓ known for small ACₙ).
- **M10 — Strong connectivity. ✅ Done (2026-06-11).** `invariants/strong.v` (§3.3). *Exit:*
  `sink_scc_reduction` producing H with the four properties; cut-crossing
  lemma.
- **M11 — The kernel. ✅ Done (2026-06-11).** `applications/ck3/lemma7.v` (§3.4). *Exit:* `lemma7`
  general in δ, plus `ck_theorem4_oriented`, `ck_conj1_delta2`;
  axiom-free.
- **M12 — Endgame + wrap-up. ✅ Done (2026-06-11). PROJECT COMPLETE; all 7 exit theorems axiom-free.** (File named ck3_main.v to avoid the k5 main.v module clash.) `applications/ck3/{endgame,main}.v`
  (§3.5). *Exit:* `ck_conj1_delta3`; full axiom audit; CHANGELOG/README/
  DESIGN updates; CI green. **Done.**

Effort calibration against k5: M8–M10 ≈ the M1–M2 band (infrastructure,
mostly smooth); M11 ≈ obstructions.v-scale (path surgery under many side
conditions — the dependent-rewrite and section-discharge lessons apply);
M12 ≈ cells.v-scale (named-vertex case analysis, pleasant).

## 5. Decisions — all RESOLVED 2026-06-11 (recommended options)

- **D8 — directed-path layer. ✅ RESOLVED:** reuse
  `GraphTheory/core/digraph.v` (`pathp`/`upath` over MathComp `path`) via
  a relType projection, mirroring `to_GT`; fall back to our own seq-based
  layer only if the projection fights us (k5 lesson: alias/canonical
  mismatches are the risk; the sgraph interop pattern worked). The
  fallback costs ≈ a week of re-proving concatenation/splitting lemmas.
- **D9 — `Oriented` in the hierarchy. ✅ RESOLVED:** a genuine HB
  structure `DiGraph ≤ Oriented ≤ Tournament` with a factory so existing
  tournament instances acquire it silently. Fallback: a mixin-free
  boolean predicate `orientedb` + hypothesis threading (uglier statements,
  zero hierarchy risk).
- **D10 — generality of the kernel. ✅ RESOLVED:** Lemma 7 uniform in δ
  (argued in §2). Fallback if the general bookkeeping drags: freeze δ = 3
  in M11 and keep Theorem 4/δ=2 out of scope.
- **D11 — statement form. ✅ RESOLVED:** Final theorem as `6 <= ell D` with
  `0 < #|D|`, plus a `exists p, dipath p /\ size p = 6`-style unfolded
  corollary for external consumption. Conjecture-1-shaped restatement
  `2 * 3 <= ell D` as a named alias.

## 6. Risks

1. **Claim 11** is the deep step (auxiliary maximal path in an induced
   subgraph, farthest-back-neighbour cycle, interaction with Claim 10).
   Mitigation: dossier first (M7) with every length computed; the surgery
   kit (M9) designed against exactly this proof, not discovered during it.
2. **The arg-max path choice** (longest + maximum cycle bound) needs paths
   as a finType. Tuples `(ℓ+1).-tuple D` with a boolean simple-path
   predicate make this routine, but the kit must commit to one
   representation early (M9) — switching later is expensive.
3. **GraphTheory dipath reuse** may clash with our HB types (D8 fallback
   priced in).
4. **Convention drift** between the dossier, the paper, and the hand proof
   (arc vs vertex counts — already bitten once in the literature). The
   dossier is the single source of truth; every formal statement quotes
   its dossier item.

## 7. What this buys the library

`oriented.v`, `dipath.v`, `strong.v` are exactly the three modules the
"directed companion" library was missing for path/cycle questions (vs the
ω̄/tournament track of k5). General `lemma7` + `ck_theorem4_oriented` are
citable theorems from a 2024 SIDMA paper; `ck_conj1_delta3` is a new
result. The δ = 4 program (k4_n10/n11 docs) would reuse all of M8–M11
unchanged.
