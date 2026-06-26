# K34 dossier — Conjecture 5.10 at k = 3, 4: formal-facing re-proof

**Status:** v1.0 (2026-06-11), M13 deliverable; single source of truth for
M14–M17 (`PLAN_K34.md`). Sources: `conjecture_5_10_k345_unified.md`,
`proof_omega_AC_n_C3.md`, `proof_deletion_AC_n_C3.md` (both red-team
passed). Every item below has been re-derived from scratch in OUR library
conventions; differences from the sources are notational only.

## §0 Conventions (library bindings)

- n = 2m+1, m = m'.+1 ≥ 3 on theorems (instances hypothesis-free);
  g = ACset m' = [1, m−1] ∪ {m+1} ⊆ 'Z_n; arc i→j ⟺ j−i ∈ g (`AC_arcE`).
- **Arc-facts** (for val i < val j, d := val j − val i, `acn_arc_facts.v`):
  `AC_arc_lt`: i→j ⟺ d < m ∨ d = m+1; `AC_arc_gt`: j→i ⟺ d = m ∨ d ≥ m+2
  (the doc's D = {m} ∪ [m+2, 2m]).
- **c = `band`** (k5 `cells.v`, relocated by D13): band v = 3 if val v = 0,
  2 if 0 < val v ≤ m, 1 if val v > m. (The doc's c(t) exactly.)
- **`AC_wrapF`**: val a < val b ∧ val b − val a < m ⟹ (a − b ∈ g) = false
  — "no backedge within a monotone (< m)-interval".
- C₃ = 'Z_3 with arc u→v ⟺ v = u+1 (so 0→1→2→0); ω̄(C₃) = 2; vertex set
  {0,1,2}. **dband h := 2 if val h = 0 else 1** (the doc's d).
- T4 := `lexprod_tournament (AC m') C3`; vertices (t,h); arcs: t→t' in AC,
  or t = t' and h→h' in C₃ (`lexprod_arcE`). #|T4| = 3n.
- Backedge clique under an order q (= `{perm _}` via `realize`): a set K
  where for u, v ∈ K with ltp q u v, the arc is v→u (later beats earlier);
  `omegab_at q = ω(backedge q)` and ω̄ = min (`omegabar_min`).
- C₃ internal arcs among nonzero h: 1→2 only (2→1 false: 2+1 = 0). Block-
  internal arcs from h=0: 0→1 only.

## §1 General additions (M14)

- **G1 `kcritical_proper_sub`** (`invariants/critical.v`): kcritical k T,
  S ≠ setT ⟹ ω̄(sub_tournament S) ≤ k−1.
  *Proof.* Proper S omits v; embed sub_tournament S into del_tournament v
  by val (injective, arc-preserving — the k5 `main.v` pattern verbatim);
  ω̄(del v) = k−1 by kcriticalP. ∎ *Generality: any tournament.*
- **G2 `card_clique_classes`** (general counting; any finType K, any
  f : V → nat, bound b with ∀u ∈ K, f u < b):
  #|K| = Σ_(i < b) #|[set u in K | f u == i]|.
  *Proof.* Partition counting (big_mkcond / partition by f). ∎
  *Generality: any finite set, no graph structure.*
- **G3 `C3_vertex_transitive`** (`constructions/circulant.v`):
  translations x ↦ x + t are automorphisms of C₃ (arc v == u+1 is
  translation-invariant: (v+t) == (u+t)+1 ⟺ v == u+1); transitivity by
  t := v − u. ∎
- **D13 relocation:** `radix_ltA`/`radix_lt_inv`/`radix_eq_inv` (generic
  nat radix lemmas), `band`, `band1P/2P/3P`, `band_ge1`, `band_le3`,
  `band12P`, `AC_wrapF`, `band_gap` move from `k5/cells.v` to
  `applications/acn_bands.v`; `cells.v` imports it. Statements unchanged.

## §2 The k = 4 value bound (V-items): ω̄(ACₙ[C₃]) ≤ 4

**V0 — the merged order ≺\*.** Key class κ(t,h) := band t + dband h ∈
{2,3,4,5}. Radix key: `kv (t,h) := (κ(t,h) * n + val t) * 3 + val h`
(val t < n, val h < 3 ✓ radix sound). qv := realize [rel u v | kv u < kv v]
(irrefl/trans/total: kv injective — κ determined? NO: kv injective because
(val t, val h) determines the vertex and kv determines (κ, val t, val h)
by radix; totality needs kv u ≠ kv v for u ≠ v: kv determines (t,h) ✓).
For a clique K of backedge(qv): kv u < kv v ⟹ v→u (**V-beat**, the
cells.v `beat_key` pattern). Same κ, val-lex larger beats smaller; larger
κ beats smaller κ.

Classes (sorted internally by (val t, val h)):
- κ=5: {(0,0)}. κ=4: {(0,1),(0,2)} ∪ {(t,0) : 1 ≤ t ≤ m}.
- κ=3: lows {(a,h) : 1 ≤ a ≤ m, h ∈ {1,2}} ∪ highs {(b,0) : b ≥ m+1}.
- κ=2: {(t,h) : t ≥ m+1, h ∈ {1,2}}.

s_K := #|K-members of class κ=K|; #|K| = s₂+s₃+s₄+s₅ (G2 with f = κ−2,
b = 4).

**V1 — s₅ ≤ 1.** Singleton class. ∎

**V2 — s₂ ≤ 1.** Two κ=2 members, later beats earlier:
same t: needs 2→1 in C₃ — false; different t (both > m, sorted by val t):
backedge t'→t with 0 < val t' − val t ≤ m−1 — `AC_wrapF`. ∎

**V3 — s₄ ≤ 2, and a 2-element κ=4 clique is {(m,0),(0,i)}, i ∈ {1,2}.**
Internal pairs: (0,1)/(0,2): needs 2→1 — false. (t,0)/(t',0), t<t' ≤ m:
AC_wrapF. (0,i)/(t,0): order (0,i) first (val 0 < val t); backedge =
arc t→0 ⟺ (0−t) = n−t ∈ g ⟺ n−t = m+1 ⟺ t = m (n−t ∈ [m+1, 2m] for
t ≤ m, and [m+1,2m] ∩ g = {m+1}). So only {(m,0),(0,i)}; no 3-subset
works ((0,1),(0,2) can't coexist). ∎

**V4 — s₃ ≤ 2; a 2-element κ=3 clique is one low (a,h) + one high (b,0)
with b−a ∈ {m} ∪ [m+2, 2m].** low/low and high/high: same t → 2→1 false;
different t → AC_wrapF (gaps ≤ m−1). low(a,h) before high(b,0) (val a ≤ m
< val b): backedge = arc b→a ⟺ (a−b) = n−(b−a) ∈ g ⟺ b−a ∈ {m} ∪
[m+2,2m] (n−x ∈ g ⟺ x ∈ {m} ∪ [m+2,2m] for x ∈ [1, 2m−1]) — i.e.
`AC_arc_gt`. ∎

**V5 — case s₄ = 2** (so K ⊇ {(m,0), (0,i)}):
- *V5a s₅ = 0*: (0,0) (κ=5, beats all) would need arc (0,0)→(m,0):
  blocks 0 ≠ m: 0→m ⟺ m ∈ g — false. ∎
- *V5b s₃ ≤ 1*: a κ=3 member is beaten by both κ=4 members.
  Low (a,h'): (m,0) beats it: a ≠ m: arc m→a ⟺ (a−m) mod n =
  m+1+a ∈ [m+2, 2m+1] — wait a ∈ [1,m]: a < m gives m+1+a ∈ [m+2, 2m] ∉ g;
  a = m: same block, internal arc (m,0)→(m,h') ⟺ 0→h' ⟺ h' = 1. So low
  = (m,1) only; but (0,i) must also beat (m,1): arc 0→m ⟺ m ∈ g — false.
  So no low; high (b,0): (0,i) beats it: arc 0→b ⟺ b ∈ g ∩ [m+1,2m] =
  {m+1}: b = m+1 only. Hence s₃ ≤ 1. ∎
  Total: |K| ≤ 0 + 2 + 1 + 1 = 4. ∎

**V6 — case s₄ ≤ 1**: if |K| ≥ 5 then by caps s₅ = 1, s₄ = 1, s₃ = 2,
s₂ = 1 (each at cap; arithmetic). Then:
- (0,0) ∈ K beats everything below.
- the κ=3 high: (0,0)→(b,0) ⟹ b = m+1 (as in V5b).
- the κ=3 low: V4 pairing with b = m+1: m+1−a ∈ {m} ∪ [m+2,2m] ⟹
  m+1−a = m ⟹ a = 1 (m+1−a ≤ m for a ≥ 1).
- the κ=2 member (e,f): (0,0)→(e,f) ⟹ e ∈ g ∩ [m+1,2m] ⟹ e = m+1;
  and the κ=3 high (m+1,0) beats it: same block: 0→f ⟹ f = 1. So (m+1,1).
- **Contradiction**: the κ=3 low (1,h) must beat the κ=2 member (m+1,1)
  (κ 3 > 2): arc 1→(m+1) ⟺ (m+1−1) = m ∈ g — false. ∎

**V7 — conclusion.** Every backedge-qv clique has ≤ 4 elements:
`omegab_at qv ≤ 4`, so ω̄(T4) ≤ 4; with ≥ 4 (M14), **ω̄(ACₙ[C₃]) = 4**. ∎

## §3 The k = 4 deletion bound (D-items): ω̄(T4 − (0,0)) ≤ 3

**D0 — the `d_then_c` order.** On the subtype del := T4 − (0,0):
`kd (t,h) := (((dband h) * 4 + band t) * n + val t) * 3 + val h`
(band ≤ 3 < 4 ✓ radix sound), order qd := realize on del via val.
Bands by (dband, band): B1 = (1,1): h ≠ 0, t > m; B2 = (1,2): h ≠ 0,
0 < t ≤ m; B3 = (1,3): h ≠ 0, t = 0; B4 = (2,1): h = 0, t > m;
B5 = (2,2): h = 0, 0 < t ≤ m. ((2,3) is the deleted (0,0).)
Band order: B1 < B2 < B3 < B4 < B5; later beats earlier (D-beat).
βd ∈ {0..4} as the class function; a₁ := |K ∩ (B1∪B2∪B3)|,
a₂ := |K ∩ (B4∪B5)|; #|K| = a₁ + a₂ (G2).

**D1 — ≤ 1 per band** (so a₁ ≤ 3, a₂ ≤ 2). Within a band: same block →
needs 2→1 (h-bands) — false — or h=0 singleton per block; different
blocks, same band-interval (t-range [1,m] or [m+1,2m], gap ≤ m−1) →
AC_wrapF. B3 has one block (t=0): two members (0,1),(0,2) need 2→1 —
false. ∎

**D2 — (3,1)-exclusion: a₂ ≥ 1 ⟹ a₁ ≤ 2.** Suppose a₁ = 3: members
(t₁,h₁) ∈ B1, (t₂,h₂) ∈ B2, (0,h₃) ∈ B3, and some (s,0) ∈ B4 ∪ B5
(s ∈ [1,2m] ∖ ... any) beats all three. First the B-chain forces blocks:
- B3 beats B1: arc 0→t₁ ⟺ t₁ ∈ g ∩ [m+1,2m] ⟹ t₁ = m+1.
- B3 beats B2: arc 0→t₂ ⟺ t₂ ∈ g ∩ [1,m] ⟹ t₂ ≤ m−1.
- B2 beats B1: arc t₂→(m+1) ⟺ m+1−t₂ ∈ g: m+1−t₂ ∈ [2,m]: ∈ g ⟺
  m+1−t₂ ≤ m−1 ⟺ t₂ ≥ 2. So t₂ ∈ [2, m−1].
Now split on s (note s ∉ {0}; s may equal a block):
- *s ∈ [1, m−1] ∪ {m+1}*: (s,0) beats (0,h₃) needs (0−s) = n−s ∈ g;
  n−s ∈ [m+2, 2m] (s ≤ m−1) or = m (s = m+1) — neither in g. ✗
- *s = m*: beats (t₂,h₂): t₂ ≠ m (t₂ ≤ m−1): arc m→t₂ ⟺ (t₂−m) mod n =
  m+1+t₂ ∈ [m+3, 2m] ∉ g. ✗
- *s ∈ [m+2, 2m]*: beats (m+1,h₁): s ≠ m+1: arc s→(m+1) ⟺
  (m+1−s) mod n = 3m+2−s ∈ [m+2, 2m] ∉ g. ✗
(If s equals a member's block, the internal arc (s,0)→(s,h) needs h = 1
and is COVERED: the three refutations above never used the internal case
because s ∉ {0} always, s = m ≠ t₂, and s ≥ m+2 ≠ m+1.) ∎

**D3 — the (2,2)-lemma: a₂ = 2 ⟹ a₁ ≤ 1.** K ∩ (B4∪B5) = {(s,0), (s',0)},
s ∈ [m+1,2m], s' ∈ [1,m]; B5 beats B4: arc s'→s ⟺ δ := s−s' ∈ g (here
δ = val s − val s' as nat, 1 ≤ δ ≤ 2m−1).
X := {h≠0 vertices beaten by both} ⊇ K ∩ (B1∪B2∪B3). Show X is
backedge-qd-independent.
- *D3a (t = s' impossible)*: (s,0) beats (s',·) needs arc s→s' ⟺
  (s'−s) = n−δ ∈ g: δ ∈ [1,m−1] → n−δ ∈ [m+2,2m] ∉ g; δ = m+1 → n−δ = m
  ∉ g; (δ = m ∉ g already). Never. ∎
- *D3b (membership shape)*: (t,h) ∈ X with t ≠ s: b := (t−s) mod n
  satisfies b ∈ g ∧ (b+δ) mod n ∈ g [arc s→t ⟺ b ∈ g; arc s'→t ⟺
  (t−s') = b+δ mod n ∈ g]. t = s: internal: only (s,1) ∈ X (b = 0).
- *D3c (split)*: t = s + b without wrap (t ≤ 2m): t ∈ [s, 2m] — band B1;
  with wrap: t = s+b−n ∈ [0, m]: t = 0 → B3, t ∈ [1,m] → B2 (t = m only
  if ≠ s', see D3f).
- *D3d (within B1, within B2: forward)*: gaps ≤ m−1, AC_wrapF. (B1 blocks
  ⊆ [s, 2m], spread ≤ 2m−s ≤ m−1; B2 blocks ⊆ [1,m], spread ≤ m−1;
  same-block pairs need 2→1.) ∎
- *D3e (cross B1–B2 dies — the CORE)*: t₁ = s+b₁ (b₁ ∈ {0} ∪ g),
  t₂ = s+b₂−n (b₂ ∈ g). Wrap forces b₂ ≥ n−s > 2m−s ≥ b₁ (no-wrap), so
  b₁ < b₂. B2 beats B1: arc t₂→t₁ ⟺ (t₁−t₂) mod n = (b₁−b₂) mod n =
  n+b₁−b₂ ∈ g; b₁−b₂ ∈ [−(m+1), −1] so n+b₁−b₂ ∈ [m, 2m]; ∩ g = {m+1} ⟹
  b₂ = b₁ + m. b₁ = 0 ⟹ b₂ = m ∉ g ✗. b₁ ∈ g ⟹ b₁+m ∈ [m+1, 2m+1] ∩ g
  = {m+1} ⟹ b₁ = 1, b₂ = m+1. X-membership then needs **1+δ ∈ g AND
  (m+1+δ) mod n ∈ g**. Core incompatibility:
  1+δ ∈ g ⟺ δ ∈ [1, m−2] (1+δ ∈ [1,m−1] ⟺ δ ≤ m−2; 1+δ = m+1 ⟺ δ = m ∉ g);
  (m+1+δ) mod n ∈ g ⟺ δ = m+1 (δ ∈ [1,m−1] → m+1+δ ∈ [m+2,2m] ∉ g;
  δ = m+1 → m+1+δ = n+1 ≡ 1 ∈ g). Disjoint. ✗ ∎
- *D3f (the B3 sub-case)*: a B3 vertex (0,h) ∈ X needs b = n−s ∈ g and
  (0−s') = n−s' ∈ g ⟹ s' = m (n−s' ∈ [m+1,2m] ∩ g = {m+1}). Then:
  (i) no B2 vertex in X: wrapped t ∈ [1, m−1] needs (t−s') = (t−m) mod n
  = m+1+t ∈ [m+2, 2m] ∉ g ✗; t = m = s' is excluded by D3a.
  (ii) the B3 vertex beats no B1 member of X: arc 0→t₁ ⟺ t₁ ∈ g ⟹
  t₁ = m+1; but m+1 ∉ X-blocks: t₁ = s would need s = m+1, then
  b = n−s = m ∉ g (no B3 vertex at all, contradiction with its
  existence); t₁ = s+b₁ generic needs b₁ = (m+1−s) mod n = 3m+2−s ∈
  [m+2, 2m] ∉ g for s ∈ [m+2, 2m] ✗.
  (iii) two B3 vertices: same block, 2→1 ✗. And nothing in X is ABOVE B3
  (X ⊆ B1∪B2∪B3). So the B3 vertex is isolated in X. ∎
- *Conclusion D3*: X independent (D1-style per band + D3e cross B1–B2 +
  D3f isolating B3), so a₁ ≤ 1. ∎

**D4 — conclusion.** a₂ = 0 ⟹ |K| = a₁ ≤ 3; a₂ = 1 ⟹ ≤ 2+1; a₂ = 2 ⟹
≤ 1+2. `omegab_at qd ≤ 3`, so ω̄(T4 − (0,0)) ≤ 3; with ≥ 3 (M14) and
vertex-transitivity (G3 + `lexprod_vertex_transitive` + `omegabar_del_vt`):
**ω̄(T4 − v) = 3 for every v**. ∎

## §4 Lower bounds and packaging (M14, M17)

- **L1** ω̄(T4) ≥ 4: `omegabar_lexprod_ge` + ω̄(AC) = 3 + ω̄(C₃) = 2.
- **L2** ω̄(T4 − (0,0)) ≥ 3: embed AC into the deletion by t ↦ (t, 1)
  (injective; arc-preserving: blocks always differ; never hits (0,0));
  `omegabar_embed` + ω̄(AC) = 3.
- **P1** `T4_kcritical4` := vt_kcritical at (0,0) with V7, D4, L1, L2.
- **P2** `card_T4` = 3n (card_lexprod, card_AC, card_C3; order: #|AC×C3| =
  n*3).
- **P3** k=3 and k=4 packaging via G1 (`kcritical_proper_sub`), mirroring
  the k5 statements; the headline `conjecture_5_10_at_345` by case
  analysis on k ∈ {3,4,5} delegating to the three families (witness sizes
  n, 3n, n² with the same `maxn 2 N` trick).

## §5 Landmines / conventions pinned

1. All key/band comparisons are NAT comparisons of radix keys; the
   k5 radix lemmas (`radix_ltA` etc.) drive every "later beats earlier in
   class/band" extraction. Exact radixes: kv = (κ·n + t)·3 + h,
   kd = ((d·4 + c)·n + t)·3 + h.
2. (0−s) mod n = n − s for 0 < s < n (val arithmetic via `val_sub_gt`-
   style lemmas; never rewrite inside 'Z_n indices — k5 lesson).
3. The C₃ facts used: 2→1 false, 0→1 true, 0→2 false, 1→2 true — all by
   computation on 'Z_3 (`arcC3E` + case analysis).
4. D2's s-split covers s ∈ [1,2m] as [1,m−1] ∪ {m} ∪ {m+1} ∪ [m+2,2m]
   (the first and third merged in the doc; we keep 4 explicit ranges).
5. In D3e the bound b₁ ≤ 2m−s ≤ m−1 uses s ≥ m+1; b₂ ≥ n−s ≥ 1 uses
   s ≤ 2m. The forced b₂ = b₁+m equation is in NAT (no wrap: b₁ ≤ m−1,
   b₂ ≤ m+1 ✓).

## §6 Oracle coverage (scripts/k4_oracle.py)

Bounds strategy (exact min-over-orders is infeasible at 3n ≥ 21; the
source project's own `verify_4critical_n21.py` used orders + SAT):
upper bounds by the explicit kv/kd orders (`omega_of_order`), lower
bounds by SAT — the "no backedge K_k" CNF UNSAT under two independent
solvers ⟹ ω̄ ≥ k; exact `omega_vec` only on the factors (ACₙ, C₃).
Crosscheck: AC₇[C₃] ≅ circulant(21, {1,2,4,7,8,9,11,15,16,18}) via CRT —
the tournament `verify_4critical_n21.py` independently certified
4-critical (SAT under Cadical + Minisat).

| Item | Check |
|---|---|
| construction | AC[C₃] lexprod is a tournament; vertex-transitivity by the two shift automorphisms (m ≤ 12); CRT iso at m = 3 |
| factors | exact: ω̄(ACₙ) = 3, ω̄(ACₙ−v) = 2 (n = 7, 9), ω̄(C₃) = 2 — feeds L1/L2 |
| headline | ω̄(T4) = 4 and ω̄(T4−(0,0)) = 3 for m = 3, 4: kv/kd orders (≤) + SAT (≥) |
| V0/D0 keys | keys injective (m = 3, 4); class sizes match definitions (m ≤ 12) |
| V1–V4 caps | enumerate within-class pairs: no backedge except the listed ones (m ≤ 12) |
| V5/V6, D4 | the kv order's backedge clique number is exactly 4; the kd order's exactly 3 (m ≤ 5) |
| D1 | within-band pairs forward under kd (m ≤ 12) |
| D2 | full s-split: no (s,0) dominates blocks {0, t₂, m+1}, t₂ ∈ [2,m−1] (m ≤ 12) |
| D3 | X backedge-independent for all (s, s') with δ ∈ g (m ≤ 12); core incompatibility ¬(1+δ ∈ g ∧ m+1+δ ∈ g) (m ≤ 39) |

Suite: `scripts/test_k4_oracle.py` — 114 tests green
(`uv run --with pytest --with networkx --with python-sat python3 -m
pytest scripts/test_k4_oracle.py -q`).
