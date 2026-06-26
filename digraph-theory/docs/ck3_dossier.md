# CK3 dossier — the δ = 3 path theorem, ready for formalization

**Status:** v1.0 (2026-06-11), M7 deliverable. This document is the single
source of truth for milestones M8–M12 (see `PLAN_CK3.md`): every formal
statement in the Rocq development cites an item ID from here. It is a
self-contained re-proof of

> **MAIN.** Every nonempty oriented graph D with d⁺(v) ≥ 3 for all v
> contains a directed simple path with 6 arcs.

combining `k3_hand_proof.md` (audited in `CORRECTNESS_REVIEW_2026_05_18.md`)
with the proof internals of Cheng–Keevash Lemma 7 (arXiv:2402.16776v4 §4,
verbatim excerpts in `paper/ck3_excerpts.md`). Differences from those
sources are deliberate and listed in §4 (landmines) and §5 (streamlinings).

Every item carries: statement, full proof, *generality class* (per D12:
the weakest hypotheses under which it is true), and *formal home*.

---

## §0 Conventions

- **Digraph** D: finite vertex type V with a boolean arc relation
  `u --> v`. No hypotheses unless stated. n := |V(D)|.
- **Oriented**: irreflexive (`~~ (u --> u)`) and antisymmetric
  (`u --> v -> ~~ (v --> u)`). Antisymmetry alone does NOT imply
  irreflexivity (u = v); keep both.
- **Path**: a nonempty sequence of *distinct* vertices p₀ p₁ … p_L with
  p_i --> p_{i+1} for all i. Its **length** is L = number of **arcs**
  (|V(P)| = L + 1). A single vertex is a path of length 0.
  MathComp realization: a pair (x, s) with `path (-->) x s && uniq (x::s)`,
  length = `size s`.
- **ℓ(D)** := the maximum length of a path of D; ℓ(D) = 0 if n = 0
  (max over the empty set). If n > 0 then ℓ(D) ≥ 0 is witnessed.
  A path of length ℓ(D) is called **maximum**; a path that cannot be
  extended by appending one vertex at its end is called **end-maximal**
  (maximum ⟹ end-maximal, not conversely).
- **Cycle** of length g: distinct vertices c₀ … c_{g−1}, g ≥ 1, with
  c_i --> c_{i+1 mod g}; g arcs, g vertices. (In an irreflexive digraph
  g ≥ 2; in an oriented digraph g ≥ 3 — we never need girth as a notion.)
- **N⁺(v)**, **d⁺(v) = |N⁺(v)|**; for A ⊆ V, **d⁺_A(v) = |N⁺(v) ∩ A|**
  (out-degree into A; for v ∈ A this is the out-degree of v in the
  induced subgraph D[A]). **δ⁺(A)** := min_{v∈A} d⁺_A(v) (only used for
  A ≠ ∅). **k-outregular**: d⁺(v) = k for all v.
- **Sub-digraph** (relation level): R ⊆ arc on the same vertex set, or an
  induced subgraph D[A] on a subtype. Both only *remove* arcs/vertices, so
  every path of the sub-digraph is a path of D and ℓ is monotone (M-ℓ
  below).
- **Strong**: for all u, v there is a directed u→v walk (fingraph
  `connect`). The empty and one-vertex digraphs are strong.

---

## §1 General toolkit (no orientedness/degree hypotheses unless stated)

### M-ℓ (monotonicity). Formal home: `core/dipath.v`.
If every arc of D′ is an arc of D and every vertex of D′ is a vertex of D
(sub-relation on the same carrier, or induced subtype), then any path of D′
is a path of D, and ℓ(D′) ≤ ℓ(D).
*Proof.* Immediate from the definitions (for the subtype case, map the
path through `val`, which preserves arcs and distinctness). ∎
*Generality:* any digraph.

### O1 (oriented average bound). Formal home: `core/oriented.v`.
Let D be oriented and ∅ ≠ A ⊆ V. Then some x ∈ A has
d⁺_A(x) ≤ (|A| − 1) / 2 (integer division). Consequently:
(a) δ⁺(A) ≤ ⌊(|A|−1)/2⌋; (b) if every v ∈ A has d⁺_A(v) ≥ k then
|A| ≥ 2k + 1; (c) a nonempty oriented D with d⁺(v) ≥ k everywhere has
n ≥ 2k + 1.
*Proof.* Σ_{v∈A} d⁺_A(v) = #(arcs of D[A]). In an oriented graph each
unordered pair {u, v} ⊆ A carries at most one arc, so the sum is
≤ C(|A|, 2) = |A|(|A|−1)/2. The minimum is at most the average:
min ≤ ⌊(|A|−1)/2⌋ (with |A| ≥ 1). For (b): k ≤ ⌊(|A|−1)/2⌋ gives
2k ≤ |A| − 1. (c) is (b) with A = V. ∎
*Generality:* any oriented digraph, any subset, any k.

### O2 (out-selection / k-outregular sub-relation). Formal home: `core/oriented.v`.
Let D be any digraph and k with d⁺(v) ≥ k for all v. Then there is a
sub-relation R ⊆ arc with d⁺_R(v) = k for all v. If D is oriented, so is
(V, R).
*Proof.* For each v choose (by finite choice) a k-subset S_v ⊆ N⁺(v)
(possible as |N⁺(v)| ≥ k); set R u v := (v ∈ S_u). Then
d⁺_R(v) = |S_v| = k. R ⊆ arc, so irreflexivity and antisymmetry are
inherited. ∎
*Generality:* any digraph, any k.

### S1 (sink-SCC trick). Formal home: `invariants/strong.v`.
Let D be a digraph with n > 0. Call A ⊆ V **closed** if u ∈ A and
u --> w imply w ∈ A. Let R(x) := { y | connect x y } (reachable set,
x ∈ R(x)). Then:
(a) every R(x) is closed and nonempty;
(b) if x* minimizes |R(x)| over all x ∈ V, then W := R(x*) is closed,
nonempty, and D[W] is strong;
(c) for a closed W, each v ∈ W has the same out-neighbourhood in D[W] as
in D: d⁺_{D[W]}(v) = d⁺_D(v); in particular out-regularity is preserved,
and D[W] is an induced subgraph (so orientedness is preserved and M-ℓ
applies).
*Proof.* (a) Reachability is transitive and arc-extends. (b) Take
y, z ∈ W; we must connect y to z inside W. Since y ∈ R(x*) we get
R(y) ⊆ R(x*) (transitivity), and minimality gives |R(y)| ≥ |R(x*)|,
hence R(y) = R(x*) ∋ z: there is a y→z walk in D; all its vertices lie
in R(y) ⊆ W, so it is a walk of D[W]. (c) Closedness puts every D-out-
neighbour of v ∈ W inside W. ∎
*Generality:* any digraph. (No general SCC theory needed.)

### S2 (cut-crossing). Formal home: `invariants/strong.v`.
Let D be strong, ∅ ≠ A ⊊ V. Then there are u ∉ A and c ∈ A with
u --> c (an arc entering A), and symmetrically one leaving A.
*Proof.* Pick w ∉ A, c₀ ∈ A and a w→c₀ walk (strongness). The walk
starts outside A and ends inside; the first arc crossing into A is the
witness. The leaving arc: same with a c₀→w walk. ∎
*Generality:* any strong digraph.

### R (the reduction). Formal home: `invariants/strong.v`.
Let D be oriented, n > 0, with d⁺(v) ≥ k for all v. Then there is a
digraph H — an induced subgraph of an arc-sub-relation of D — such that:
H is oriented, strong, k-outregular, every path of H is a path of D
(hence ℓ(H) ≤ ℓ(D)), and |V(H)| ≥ 2k + 1.
*Proof.* Apply O2 to get H₁ = (V, R), oriented, k-outregular, with
ℓ(H₁) ≤ ℓ(D) (M-ℓ). Apply S1 to H₁: W := R(x*) gives H := H₁[W],
strong, induced-closed so still k-outregular (S1c) and oriented;
ℓ(H) ≤ ℓ(H₁) ≤ ℓ(D) (M-ℓ). |V(H)| ≥ 2k+1 by O1(b) applied to A = W
inside the oriented H. ∎
*Note:* the hand proof's R1 (a first sink SCC of D itself) is redundant —
it was only needed there to pin ℓ = 5 exactly via Theorem 4, which the
formal route never uses. We do R2 (= O2) then R3 (= S1).
*Generality:* any oriented digraph, any k ≥ 0 (for k = 0, H can be a
single vertex; all claims hold).

### K-A (Lemma A, endpoint closure). Formal home: `core/dipath.v`.
Let P = v₀ … v_L be a **maximum** path of D with last vertex v_L. Then
N⁺(v_L) ⊆ V(P).
*Proof.* If v_L --> w with w ∉ V(P) then P·w is a path of length L+1,
contradicting L = ℓ(D). ∎
*Generality:* any digraph. (Also true for end-maximal paths; state for
those and derive the maximum case — the end-maximal form is what K-11
needs inside the induced subgraph.)

### K-Ext (maximal extension). Formal home: `core/dipath.v`.
In any digraph, every vertex x is the first vertex of some end-maximal
path. *Proof.* Greedy extension terminates (lengths are bounded by n−1);
formally: take a path starting at x of maximum length among such, which
exists since the set is nonempty (the trivial path) and finite. ∎
*Generality:* any digraph.

### K-D (endpoint cycle). Formal home: `core/dipath.v`.
Let P = v₀ … v_L be a maximum path, and suppose d⁺(v_L) ≥ 1. Let
I := { i ≤ L : v_L --> v_i } (nonempty by K-A; L ∉ I if D is
irreflexive — assume irreflexive here), and a := min I. Then
C := v_a v_{a+1} … v_L (v_a) is a cycle with |V(C)| = L − a + 1, and
a ≤ L − d⁺(v_L), i.e. |V(C)| ≥ d⁺(v_L) + 1.
*Proof.* C is a cycle: consecutive path arcs plus the closing arc
v_L --> v_a; vertices distinct as a sub-sequence of P. The map
i ↦ v_i is injective from I into N⁺(v_L) and surjective by K-A, so
|I| = d⁺(v_L); I ⊆ {0, …, L−1} (irreflexivity), so its minimum is
≤ L − |I|. ∎
*Generality:* any irreflexive digraph.
**Definition (cycle bound).** The cycle bound of a maximum path P is
|V(C)| = L − min I + 1 (defined whenever d⁺(v_L) ≥ 1). Larger cycle
bound = smaller a.

### K-a1 (a ≥ 1). Formal home: `applications/ck3/lemma7.v` (or dipath.v).
Let D be strong with a maximum path P = v₀ … v_L, d⁺(v_L) ≥ 1,
irreflexive, and n ≥ L + 2. Then a := min I ≥ 1.
*Proof.* Suppose a = 0. Then C (from K-D) has vertex set
{v₀, …, v_L} = V(P), of size L + 1 < n, so V ∖ V(C) ≠ ∅. V(C) is a
proper nonempty subset; by S2 there is an arc u --> c with u ∉ V(C),
c ∈ V(C). Unroll C from c: the path
u, c, c⁺, …, (around C) …, c⁻ has length 1 + (L+1−1) = L + 1 > ℓ(D),
contradiction. ∎
*Generality:* any strong irreflexive digraph with n ≥ ℓ(D) + 2.

### K-10 (disjoint cycles force long paths — positive form). Formal home: `applications/ck3/lemma7.v` (statement general; could live in strong.v).
Let D be strong and let C₁, C₂ be vertex-disjoint cycles. Then
ℓ(D) ≥ |C₁| + |C₂| − 1.
*Proof.* Among all paths starting in V(C₁) and ending in V(C₂) (nonempty:
strongness connects any u₁ ∈ C₁ to any u₂ ∈ C₂, and a shortest u₁→u₂
walk is a path; it starts in C₁ and ends in C₂), choose Q = q₀ … q_t of
**minimum length**. Then t ≥ 1 (the cycles are disjoint) and no internal
or non-endpoint vertex of Q revisits the cycles: if q_j ∈ V(C₁) for some
j ≥ 1, the suffix q_j … q_t is shorter; if q_j ∈ V(C₂) for some
j ≤ t−1, the prefix q₀ … q_j is shorter. Now concatenate: unroll C₁
ending at q₀ (a path with |C₁| vertices, |C₁| − 1 arcs, ending at q₀),
then Q (t ≥ 1 arcs), then unroll C₂ starting at q_t (|C₂| − 1 arcs).
All three vertex sets are pairwise disjoint (C₁ ∩ C₂ = ∅; internal Q
vertices avoid both; q₀ only in C₁, q_t only in C₂), so the result is a
path of length (|C₁| − 1) + t + (|C₂| − 1) ≥ |C₁| + |C₂| − 1. ∎
*Generality:* any strong digraph. (The contradiction form used below:
in the kernel setting ℓ ≤ 2δ, there are no two disjoint cycles each of
length ≥ δ + 1, since they would give ℓ ≥ 2δ + 1.)

---

## §2 The kernel (Cheng–Keevash Lemma 7 and its internals)

**Kernel setting (KS).** Fixed for K-11 … K-count:
- H oriented, strong, δ-outregular with δ ≥ 1, and ℓ := ℓ(H) ≤ 2δ;
- n_H ≥ 2δ + 1 (automatic from O1(c) — recorded as a hypothesis to keep
  the section self-contained);
- P = v₀ … v_ℓ a maximum path chosen, among all maximum paths, with
  **maximum cycle bound** (well-defined: d⁺(v_ℓ) = δ ≥ 1, so every
  maximum path has a cycle bound by K-D; choose by arg max over the
  finite set of maximum paths);
- I, a, C as in K-D. Facts available immediately:
  |V(C)| = ℓ − a + 1 ≥ δ + 1 (K-D), and a ≥ 1 whenever ℓ ≤ 2δ − 1
  (K-a1′ below; at the boundary ℓ = 2δ the inequality n_H ≥ ℓ + 2 can
  fail and a = 0 genuinely occurs, e.g. Hamilton cycles in R₇).

**K-a1′ (a ≥ 1 in KS).** If ℓ ≤ 2δ − 1, then n_H ≥ 2δ + 1 = (2δ−1) + 2
≥ ℓ + 2 and K-a1 applies, so a ≥ 1. For the boundary case ℓ = 2δ
(only used for oracle checks of K-11/K-12, never in the final proofs):
add n_H ≥ 2δ + 2 as an explicit hypothesis, or restrict the oracle to
instances where a ≥ 1 holds. **The formal kernel section assumes
ℓ ≤ 2δ − 1** (all in-development uses have ℓ ≤ 2δ − 1; the K-11 proof
itself is valid whenever ℓ ≤ 2δ, see its proof).

### K-11 (Claim 11: the predecessor's out-neighbours are on P). Formal home: `applications/ck3/lemma7.v`.
In KS: N⁺(v_{a−1}) ⊆ V(P).
*Proof.* Suppose w₁ ∈ N⁺(v_{a−1}) ∖ V(P). Let H₁ := H[V ∖ V(P)]
(nonempty: w₁). By K-Ext take an end-maximal path P₁ = w₁ … w_m
(m ≥ 1) of H₁ starting at w₁.

*Step 1: N⁺(w_m) ∩ V(C) = ∅.* Suppose w ∈ N⁺(w_m) ∩ V(C). Then
v₀ … v_{a−1} w₁ … w_m w (around C) w⁻
— i.e. the v-prefix (a−1 arcs), the arc v_{a−1}→w₁, P₁ (m−1 arcs), the
arc w_m→w, then C unrolled from w to its C-predecessor w⁻
(|V(C)|−1 arcs) — is a path: its three vertex blocks
{v₀,…,v_{a−1}}, V(P₁), V(C) are pairwise disjoint
(V(P₁) ∩ V(P) = ∅; the v-prefix and V(C) partition V(P)). Its length is
(a−1) + 1 + (m−1) + 1 + (ℓ − a + 1 − 1) = ℓ + m ≥ ℓ + 1 > ℓ(H).
Contradiction.

*Step 2: locating N⁺(w_m).* P₁ end-maximal in H₁ puts every
out-neighbour of w_m that lies outside V(P) inside V(P₁). With Step 1
and V(P) = {v₀,…,v_{a−1}} ⊎ V(C):
N⁺(w_m) ⊆ {v₀, …, v_{a−1}} ∪ V(P₁).

*Step 3: the long cycle C₁.* P₂ := v₀ … v_{a−1} w₁ … w_m is a path
(a + m vertices; the joining arc is v_{a−1} → w₁). All δ out-neighbours
of w_m lie on P₂ and are distinct from w_m. Measure the **distance** of
z ∈ N⁺(w_m) as (position of w_m on P₂) − (position of z). Distances are
≥ 1, distinct, and **distance 1 is impossible**: the distance-1 vertex
is the P₂-predecessor of w_m (w_{m−1}, or v_{a−1} if m = 1), and the
path arc predecessor → w_m together with w_m → predecessor would be an
antiparallel pair — H is oriented. So the δ distances are distinct
values ≥ 2, hence max distance ≥ δ + 1. Let z realize the maximum;
C₁ := z … w_m (z) (the P₂-segment from z to w_m plus the arc w_m → z)
is a cycle of length ≥ δ + 2.

*Step 4: contradiction.* V(C₁) ⊆ V(P₂) = {v₀,…,v_{a−1}} ∪ V(P₁) is
disjoint from V(C). Both cycles have length ≥ δ + 1 (C by K-D, C₁ by
Step 3), so K-10 gives ℓ(H) ≥ (δ+1) + (δ+1) − 1 = 2δ + 1 > 2δ ≥ ℓ.
Contradiction. ∎
*Generality:* KS with ℓ ≤ 2δ (note: the proof has one arc of slack —
C₁ ≥ δ+2 where δ+1 is needed — kept as δ+2 because it is what the
antiparallel argument naturally gives; see Landmine 2, §4).

### K-AB (the partition at v_{a−1}). Formal home: `applications/ck3/lemma7.v`.
In KS define A := N⁺(v_{a−1}) ∩ {v₀, …, v_{a−1}},
B := N⁺(v_{a−1}) ∩ V(C). Then:
(a) N⁺(v_{a−1}) = A ⊎ B and |A| + |B| = δ;
(b) v_{a−1} ∉ A (irreflexivity), so |A| ≤ a − 1, i.e. a ≥ |A| + 1;
(c) v_a ∈ B (the path arc v_{a−1} → v_a, and v_a ∈ V(C)), so B ≠ ∅.
*Proof.* (a) K-11 plus V(P) = {v₀,…,v_{a−1}} ⊎ V(C); the union is
disjoint because the two index ranges are. (b), (c) immediate. ∎

### K-B⁻ (the predecessor set). Formal home: `applications/ck3/lemma7.v`.
In KS, the C-predecessor map pred_C (v_a ↦ v_ℓ, v_{i+1} ↦ v_i for
a ≤ i < ℓ) is a bijection of V(C). Define B⁻ := pred_C(B) ⊆ V(C)
(equivalently: u ∈ B⁻ iff u ∈ V(C) and the C-arc out of u lands in B).
Then |B⁻| = |B| ≥ 1, and v_ℓ ∈ B⁻ whenever v_a ∈ B — in particular
**v_ℓ ∈ B⁻ always** (K-AB c).
*Formal note:* realize pred_C concretely on indices, no permutation
theory: pred(i) = if i == a then ℓ else i − 1.

### K-12 (Claim 12: B⁻'s out-neighbours stay on C). Formal home: `applications/ck3/lemma7.v` (general form possibly in `core/dipath.v`).
**General form (D12):** in **any digraph**, let P be a maximum path of
maximum cycle bound with a ≥ 1, and B, B⁻ as in K-AB/K-B⁻ (defined from
P alone). Then for every b ∈ B⁻, N⁺(b) ⊆ V(C). — The proof below uses
no orientedness, no degree hypothesis, no strongness and no bound on ℓ;
this form is directly oracle-checked on random non-oriented digraphs
(§6). In KS it specializes to the paper's Claim 12.
*Proof.* Let b ∈ B⁻ with C-successor b⁺ ∈ B (definition of B⁻), and
suppose b --> w with w ∉ V(C). Two cases.

*Case w ∉ V(P).* Then
v₀ … v_{a−1} b⁺ (around C) b w — the v-prefix (a−1 arcs), the arc
v_{a−1} → b⁺ (b⁺ ∈ B ⊆ N⁺(v_{a−1})), C unrolled from b⁺ to b
(|V(C)|−1 arcs; it ends at b because b⁺ is b's successor), then b → w —
is a path of length (a−1) + 1 + (ℓ−a) + 1 = ℓ + 1 > ℓ. Contradiction.

*Case w = v_i, 0 ≤ i ≤ a−1.* Let
P′ := v₀ … v_{a−1} b⁺ (around C) b — as above but stopping at b. Its
length is (a−1) + 1 + (ℓ−a) = ℓ, so P′ is also a maximum path; its last
vertex is b. By K-A (applied to P′), N⁺(b) ⊆ V(P′), and d⁺(b) = δ ≥ 1,
so P′ has a well-defined cycle bound (K-D). The arc b → v_i shows the
minimum back-arc index of P′ is ≤ i (v_i sits at position i on P′,
same as on P). Hence the cycle bound of P′ is
≥ (position of b) − i + 1 = ℓ − i + 1 ≥ ℓ − (a−1) + 1 = |V(C)| + 1,
strictly larger than the cycle bound |V(C)| of P. This contradicts the
choice of P (maximum cycle bound among maximum paths). ∎
*Generality:* any digraph (see the general form above; the
cycle-bound-maximal choice is essential). One caveat for the case
analysis: "w ∉ V(C)" splits into w ∉ V(P) and w = v_i with i ≤ a−1
because V(P) ∖ V(C) = {v₀, …, v_{a−1}} — this uses only the definition
of C as the suffix from index a.

*Remark (degree slack, D12).* K-AB, K-count and K-11 remain true with
`d⁺(v) ≥ δ` in place of `d⁺(v) = δ` (all inequalities go the right
way); exact out-regularity is needed ONLY for `|S| ≤ δ` in K-7
(|S| = |B| ≤ d⁺(v_{a−1})). The formal kernel keeps `= δ` for
simplicity, but states per-lemma hypotheses so the ≥-variants are
recoverable.

### K-count (the geometric count). Formal home: `applications/ck3/lemma7.v`.
In KS, let S := B⁻ (as a vertex set; D[S] when degrees are meant) and
s := δ⁺(S) = min_{x∈S} d⁺_S(x) (S ≠ ∅ by K-B⁻). Then:
(a) |V(C)| ≥ |S| + δ − s;
(b) ℓ ≥ 2δ − s, equivalently s ≥ 2δ − ℓ.
*Proof.* (a) Fix x ∈ S with d⁺_S(x) = s. By K-12, N⁺(x) ⊆ V(C), and
|N⁺(x)| = δ. Exactly s of these lie in S, so δ − s lie in V(C) ∖ S.
Therefore |V(C)| ≥ |S| + (δ − s).
(b) Count V(P): ℓ + 1 = |V(P)| = a + |V(C)|
≥ (|A| + 1) + (|S| + δ − s)        [K-AB(b), part (a)]
= |A| + |B| + δ − s + 1            [|S| = |B|, K-B⁻]
= 2δ + 1 − s.                      [K-AB(a)] ∎
*Landmine 1 resolved (§4): the bound is exactly s ≥ 2δ − ℓ with the
arc-length convention; there is no "+1".*

### K-7 (Lemma 7, general). Formal home: `applications/ck3/lemma7.v`.
Let D be oriented, n > 0, with d⁺(v) ≥ δ for all v. Then
ℓ(D) ≥ 2δ, **or** there is a nonempty S ⊆ V with |S| ≤ δ and
δ⁺(D[S]) ≥ 2δ − ℓ(D).
*Proof.* If δ = 0, ℓ(D) ≥ 0 = 2δ. Let δ ≥ 1 and suppose ℓ(D) ≤ 2δ − 1.
Apply R: get H oriented, strong, δ-outregular, ℓ(H) ≤ ℓ(D) ≤ 2δ − 1,
n_H ≥ 2δ + 1. H satisfies KS (with ℓ := ℓ(H) ≤ 2δ − 1). Take S := B⁻
from the kernel: |S| = |B| ≤ δ (K-AB a), S ≠ ∅, and
δ⁺(H[S]) ≥ 2δ − ℓ(H) (K-count b). The vertices of H are vertices of D
and the arcs of H[S] are arcs of D[S], so for every x ∈ S,
d⁺_{D[S]}(x) ≥ d⁺_{H[S]}(x); hence
δ⁺(D[S]) ≥ δ⁺(H[S]) ≥ 2δ − ℓ(H) ≥ 2δ − ℓ(D). ∎
*Formal interface note:* besides the bare `lemma7`, export a packaged
`kernel_witness` (KS → a record/Σ-type with P, a, C, A, B, B⁻ and the
facts K-AB, K-B⁻, K-12, K-count, |V(C)| = ℓ−a+1) — the δ = 3 endgame
consumes the package, not the bare statement.

### T4 (Cheng–Keevash Theorem 4, oriented case — corollary). Formal home: `applications/ck3/lemma7.v`.
Oriented, n > 0, d⁺ ≥ δ everywhere ⟹ ℓ(D) ≥ 2δ − ⌊(δ−1)/2⌋
(≥ ⌈3δ/2⌉, the paper's headline).
*Proof.* If ℓ(D) ≤ 2δ − ⌊(δ−1)/2⌋ − 1 then in particular
ℓ(D) ≤ 2δ − 1 (δ ≥ 1 or trivial), so K-7 yields S ≠ ∅, |S| ≤ δ, with
δ⁺(D[S]) ≥ 2δ − ℓ(D) ≥ ⌊(δ−1)/2⌋ + 1 > ⌊(|S|−1)/2⌋ ≥ δ⁺(D[S]) by
O1(a). Contradiction. ∎

### C2 (Conjecture 1 at δ = 2 — corollary). Formal home: `applications/ck3/lemma7.v`.
Oriented, n > 0, d⁺ ≥ 2 everywhere ⟹ ℓ(D) ≥ 4.
*Proof.* T4 at δ = 2: 2·2 − ⌊1/2⌋ = 4. ∎

---

## §3 The δ = 3 endgame

**Endgame setting (ES).** H from R at k = 3 (oriented, strong,
3-outregular, n_H ≥ 7), assumed ℓ := ℓ(H) = 5 — the case ℓ ≤ 4 dies in
E0; KS holds with δ = 3. Kernel package: P = v₀…v₅, a, C, A, B,
S := B⁻, s := δ⁺(H[S]).

### E0 (short lengths die). If ℓ(H) ≤ 4, contradiction.
*Proof.* KS holds (ℓ ≤ 4 ≤ 2δ−1 = 5). K-count: s ≥ 6 − ℓ ≥ 2. O1(a) on
S (|S| ≤ 3): s ≤ ⌊(3−1)/2⌋ = 1. Contradiction. ∎

### E1 (|S| = 3, every S-outdegree is 1, |A| = 0, a = 1).
*Proof.* s ≥ 6 − 5 = 1 (K-count b). If |S| ∈ {1, 2}, O1(a) gives
s ≤ ⌊(|S|−1)/2⌋ = 0 — contradiction; so |S| = 3 (|S| ≤ 3 by K-AB/K-B⁻).
Then |B| = 3, so |A| = 0 (K-AB a).
Each x ∈ S has d⁺_S(x) ≥ s ≥ 1 and Σ_{x∈S} d⁺_S(x) = #arcs(H[S]) ≤ 3
(O1's counting: oriented on 3 vertices has ≤ C(3,2) = 3 arcs); three
summands, each ≥ 1, sum ≤ 3 ⟹ **d⁺_S(x) = 1 for every x ∈ S** (hence
also s = 1).
a = 1: K-count(a) gives |V(C)| ≥ 3 + 3 − 1 = 5; |V(C)| = 6 − a, so
a ≤ 1; with a ≥ 1 (KS), a = 1. Consequently V(C) = {v₁, …, v₅},
B = N⁺(v₀), and the closing arc is v₅ → v₁. ∎
*(The hand proof's "S is a directed triangle" is not needed — only
d⁺_S ≡ 1 is used downstream.)*

### E2 (v₅ ∈ S). *Proof.* K-B⁻ with a = 1: the path arc v₀ → v₁ puts
v₁ ∈ B; pred_C(v₁) = v₅ (closing arc v₅ → v₁). ∎

### E3 (full fan-out). For every x ∈ S and every t ∈ V(C) ∖ S:
x --> t.
*Proof.* N⁺(x) ⊆ V(C) (K-12), |N⁺(x)| = 3, |N⁺(x) ∩ S| = d⁺_S(x) = 1
(E1), so |N⁺(x) ∩ (V(C) ∖ S)| = 2 = |V(C) ∖ S| (E1: |V(C)| = 5,
|S| = 3). A subset of a 2-element set with 2 elements is the whole
set. ∎

### E4 (σ-closure, one statement). For every i ∈ {1, …, 5}:
v_i ∈ S ⟹ pred_C(v_i) ∈ S.
*Proof.* Let v_i ∈ S and suppose p := pred_C(v_i) ∉ S. Then
p ∈ V(C) ∖ S, so v_i --> p by E3. But p --> v_i is an arc of C (a path
arc for i ≥ 2, the closing arc v₅ → v₁ for i = 1) — an antiparallel
pair in the oriented H. Contradiction. ∎
*(This single statement replaces the hand proof's five implications
(P1)–(P4), (C1): pred_C uniformly handles both path arcs and the
closing arc.)*

### E5 (contradiction). v₅ ∈ S (E2); applying E4 four times:
v₄, v₃, v₂, v₁ ∈ S. So |S| ≥ 5, contradicting |S| = 3 (E1). ∎
*(No permutation/orbit theory: four concrete applications of E4. The
hand proof's "only invariant subsets of a 5-cycle are ∅ and all" is
bypassed.)*

### MAIN. Formal home: `applications/ck3/main.v`.
`Theorem ck_conj1_delta3 (D : oriented) : 0 < #|D| ->
 (forall v, 3 <= outdeg v) -> 6 <= ell D.`
*Proof.* Apply R (k = 3): H oriented, strong, 3-outregular,
ℓ(H) ≤ ℓ(D), n_H ≥ 7. If ℓ(H) ≤ 5: E0 kills ℓ(H) ≤ 4 and E1–E5 kill
ℓ(H) = 5; so ℓ(H) ≥ 6 and ℓ(D) ≥ ℓ(H) ≥ 6. ∎
Corollaries: an unfolded `exists`-path form (D11), and the alias
`2 * 3 <= ell D`.

---

## §4 Landmines (resolved)

1. **The paper's "+1".** Its closing line "ℓ(D) = |P| ≥ 2δ+1−δ⁺(S)"
   uses |P| = number of *vertices*. Re-done in arc convention
   (K-count b): ℓ + 1 = |V(P)| ≥ 2δ + 1 − s, i.e. **s ≥ 2δ − ℓ —
   exactly the headline, no bonus**. The chain |A| ≤ a − 1,
   |V(P)| = a + |V(C)|, |V(C)| ≥ |S| + δ − s is tight at every step
   in the δ = 3 endgame (a = 1, |A| = 0, |V(C)| = 5 = 3 + 3 − 1).
2. **Claim 11's "δ + 2".** The paper asserts C₁ has length ≥ δ + 2
   without comment. Justification (K-11 Step 3): distance 1 from w_m on
   P₂ is its predecessor, excluded by antiparallelism (oriented). So
   distances are δ distinct values ≥ 2, max ≥ δ + 1, |C₁| ≥ δ + 2.
   Note the final contradiction only needs |C₁| ≥ δ + 1, so a formal
   fallback (if the distance-2 argument is annoying) is to prove only
   max distance ≥ δ, |C₁| ≥ δ + 1 — one arc of slack to spare. The
   paper also says "two disjoint cycles of length at least δ+2,
   contradicting Claim [10] (δ+1)" — the mismatch is harmless for the
   same reason.
3. **Empty graph.** Conjecture 1 as literally stated is false for the
   empty oriented graph (min-outdegree hypothesis vacuous, no path).
   All theorems with δ ≥ 1 carry `0 < #|D|`. K-7 carries it too (for
   n = 0 the S branch is unsatisfiable and ℓ = 0 < 2δ).
4. **Vertex vs arc length.** ℓ counts ARCS everywhere in this dossier
   and in the formal development. |V(P)| = ℓ(P) + 1; |V(C)| = (arcs
   of C). Any statement imported from the hand proof or the paper has
   been re-derived in this convention here.
5. **Paper Claim 6 is false as stated** (found by the oracle, M7). It
   asserts ℓ(D_{a,b}) = δb + a − 1; but D_{1,2} at δ = 2 contains the
   5-arc path 3→2→5→1→4→0 (oracle labelling), and ℓ(D_{1,2}) =
   2δ + 1 = (δ+1)b − 1 at δ ∈ {2, 3} (exact enumeration). The gap: the
   segment count in Claim 6's proof silently assumes a segment starting
   at v₁ (length ≤ a); if v₁ is instead the final vertex, δ full
   b-segments plus a partial first segment of length b − 1 fit.
   **Impact on us: none** — Claim 6/Proposition 2 are background (the
   girth-strengthening counterexamples), not in our proof chain. Impact
   elsewhere: the literature-notes table calling D_{1,2} an "ℓ = 2δ
   tight seed" is off by one (it is ℓ = 2δ + 1); the regular tournament
   R_{2δ+1} is the genuine tight seed. Worth reporting upstream
   (Proposition 2 for odd g needs the corrected count
   (δ+1)·(g+1)/2 − 1; the asymptotics and Conjecture 16's c ≤ 1/2 are
   unaffected... the constant changes — re-derive before citing).

## §5 Streamlinings vs the hand proof (intentional differences)

- R1 dropped (redundant; see R). Theorem 4 never used as input (E0).
- "S is a directed triangle" weakened to d⁺_S ≡ 1 (all that is used).
- Five closure implications (P1)–(P4),(C1) unified into E4 via pred_C.
- The 5-cycle invariant-subset argument replaced by four applications
  of E4 (E5).
- K-10 stated positively (ℓ ≥ |C₁| + |C₂| − 1), reusable beyond this
  proof.
- T4 comes out one better than the paper's ⌈3δ/2⌉ for even δ
  (2δ − ⌊(δ−1)/2⌋); both forms exported.

## §6 Oracle coverage map (scripts/ck3_oracle.py)

Claims are checked on: (i) random oriented digraphs (orientations of
G(n, p)); (ii) their k-outregular sink-SCC reductions (= R, the same
construction); (iii) seeds: rotational tournaments R₅, R₇ (genuinely
ℓ = 2δ, but n = ℓ+1 so a = 0 occurs — near-misses) and the lift family
D_{1,2} at δ ∈ {2, 3} (ℓ = 2δ+1 — near-miss the other way; landmine 5);
(iv) random arbitrary (non-oriented) digraphs for the general K-12.

**Kernel coverage strategy.** Genuine KS instances (strong,
δ-outregular, oriented, ℓ ≤ 2δ, n ≥ ℓ+2) are empirically unreachable —
their emptiness for δ ≤ 3 IS the theorem. So: `kernel_check` (the full
K-11/K-AB/K-B⁻/K-12/K-count suite) returns 0 on every reachable
instance but would fully verify a KS instance if one appeared (vacuity
scan asserts ℓ ≥ 2δ+1 on all k=2 reductions with n ≥ 6); the kernel's
*components* are covered separately: K-A, K-D, K-a1, K-10 on seeds and
reductions, and K-12 in its any-digraph general form on random
digraphs where it fires nontrivially.

| Item | Oracle check |
|---|---|
| O1 | min S-outdegree ≤ ⌊(|A|−1)/2⌋ on random subsets |
| O2/R | reduction output is k-outregular, strong, oriented, ℓ ≤ ℓ(D), n ≥ 2k+1 |
| M-ℓ | ℓ(reduction) ≤ ℓ(D) |
| K-A | endpoint out-neighbours on every maximum path |
| K-D | suffix cycle length = ℓ−a+1 ≥ d⁺(end)+1 |
| K-a1 | a ≥ 1 on strong instances with n ≥ ℓ+2 |
| K-10 | sampled disjoint cycle pairs: ℓ ≥ c₁+c₂−1 |
| K-12 (general form) | random arbitrary digraphs + all seeds; fires nontrivially (≥ 10 (path, b) pairs per seed batch) |
| K-11/K-AB/K-count | `kernel_check` vacuity scan (no KS instance reachable — the theorem itself); components covered via K-A/K-D/K-10/K-12 |
| E0–E5 | vacuous on real instances (none exist); negative control: theorem MAIN on every sample |
| MAIN | ℓ ≥ 6 on every random oriented sample with δ⁺ ≥ 3; ℓ ≥ 4 with δ⁺ ≥ 2 |

## §7 Formal interface summary (what each milestone proves)

- M8 `core/oriented.v`: `Oriented` structure; `outdeg`;
  `oriented_card_arcs` (Σ d⁺_A = #arcs(A) ≤ C(|A|,2));
  `oriented_avg_bound` (O1 a–c); `outregular_sel` (O2).
- M9 `core/dipath.v`: `dipath`/`ell` + witness + monotonicity (M-ℓ);
  `end_maximal`, K-Ext; K-A (end-maximal + maximum forms); K-D +
  `cycle_bound`; surgery kit: `unroll_cycle` (cycle ↦ path ending/
  starting anywhere), `cat_dipath` (disjoint concatenation),
  `take/drop` segment lemmas, `cycle_of_backarc` (path + back-arc ↦
  cycle).
- M10 `invariants/strong.v`: `strongb`; S1 (closed sets, sink trick);
  S2; `reduction` (R).
- M11 `applications/ck3/lemma7.v`: KS section; K-a1(′), K-10, K-11,
  K-AB, K-B⁻, K-12, K-count; `kernel_witness`; `lemma7` (K-7); `T4`;
  `ck_conj1_delta2` (C2).
- M12 `applications/ck3/endgame.v`: E0–E5 (consuming
  `kernel_witness` at δ = 3); `applications/ck3/main.v`:
  `ck_conj1_delta3` + corollaries; audits and docs.
