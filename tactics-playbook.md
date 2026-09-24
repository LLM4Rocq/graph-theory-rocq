# tactics-playbook.md

Running log of Rocq/SSReflect errors hit while formalising in this repository,
and the fix that worked.  Append; never rewrite history.  Read this file first.

Toolchain: Rocq 9.1.1, mathcomp (`all_boot`), `coq-graph-theory` (`GraphTheory.core`),
project logical paths `GTBase`, `Packing`, `Topological`, …

## Incremental checking

There is no `rocq-mcp-evolve` MCP server exposed in this session, so the
incremental loop used instead is: build `base/` **once**
(`cd base && rocq makefile -f _CoqProject -o Makefile.coq && make -f Makefile.coq -j4`),
then recompile **only the file under work**:

```
cd packing-theory && rocq c -R theories Packing -Q ../base/theories GTBase \
  -Q ../topological-graph-theory/theories Topological -w -notation-overridden \
  theories/foundations/fair_matching.v
```

That is ~2 s per attempt, vs. minutes for `make`.  Prefer it.

## Library location notes (saves search time)

| want | where |
|---|---|
| `E(G)`, `edgesP`, `in_edges`, `opn_edges` | `GraphTheory.core.sgraph` |
| `matching`, `vcover`, `vcoverP`, `Hall`, `Konig`, `min_vcover_matching` | `GraphTheory.core.connectivity` |
| `smallest`, `largest`, `argmin_smallest`, `ex_smallest` | `GraphTheory.core.preliminaries` |
| `Delta`, `ceil_div`, `bipartite` | `GTBase.base` |

`GTBase.base` re-exports `digraph sgraph coloring` but **not** `connectivity`
or `preliminaries` — import them explicitly.

## Errors and fixes

### 1. `The variable argmin_smallest was not found in the current environment.`
`From GraphTheory Require Import connectivity.` does **not** re-export
`preliminaries` (it `Import`s, not `Export`s).  Fix: import it by name,
`From GraphTheory Require Import preliminaries connectivity.`

### 2. `The term "covV" has type "is_true (vcover V)" while it is expected to have type "{set ?G}"`
`vcoverP` is proved inside `Section vcover` with `Variables (G : sgraph) (V : {set G})`,
so after discharge **`V` is an explicit argument**: `vcoverP V : reflect … (vcover V)`.
Writing `case/(vcoverP covV)` feeds the proof where the set is expected.
Fix: `move/(vcoverP V): covV => covP.` then `case: (covP _ _ xy)`.
General rule: a lemma living in a section that also fixes the object it talks
about usually keeps that object explicit — check with `About`.

### 3. `No assumption in ((#|C| <= #|C| + trim_excess C) = true)`
Symptom of an over-clever `split => // [|i]; [| … ]` on a three-way `[/\ _, _ & _]`:
the `//` consumed a different goal than intended and the branch list desynchronised.
Fix: name every branch explicitly,
`split; [exact: subxx | exact: (forallP allok) | exact: leq_addr].`

### 4. `The LHS of subn1 (_ - 1) does not match any subterm of the goal`
Chaining `… addKn subn1 -subn1` to massage `#|A :\ e| = #|A| - 1` fails because
`cardsD1` rewrites the *right*-hand `#|A|` too, and the normal forms
`n - 1` / `n.-1` keep flipping.  Two fixes that worked:
* state the `have` in `.-1` form: `#|(C :\ e) :&: E i| = (#|C :&: E i|).-1`,
  proved by `rewrite cardD (cardsD1 e (C :&: E i)) emem.` (the boolean
  `e \in A` rewrites to `true`, and `true + n).-1` reduces);
* for the arithmetic step, isolate it as a standalone `have` over plain naturals
  before touching cardinalities:
  `have key (a b : nat) : b < a -> (a.-1 - b).+1 <= a - b.`
  `by case: a => // a; rewrite ltnS => hb; rewrite subSn.`
  Doing arithmetic on abstract `a b : nat` avoids all higher-order/`#| |`
  unification noise.

### 5. Truncated subtraction *is* the positive part
In `nat`, `#|C :&: E i| - q i` already denotes `max(0, …)`.  Defining an excess
potential as `\sum_(i < m) (#|C :&: E i| - q i)` therefore needs no `maxn`, and
`leq_subLR : (m - n <= p) = (m <= n + p)` converts a hypothesis
`#|C :&: E i| <= q i + B` into the excess bound in one rewrite.

### 6. Strong induction on a numeric potential
Pattern that worked for "delete one element, potential drops":
```
have [n] := ubnP (trim_excess C); elim: n C => [C|n IH C]; first by rewrite ltn0.
rewrite ltnS => leC.
```
`ubnP` gives `trim_excess C < n`; the base case is discharged by `ltn0`.
Recurse with `IH (C :\ e) (leq_trans dec leC)`.

### 7. `\bigcup` cardinality
mathcomp has `leq_card_cover` for `cover P` (`P : {set {set T}}`) but **not** an
indexed-`\bigcup` version.  Three-line replacement, copying the `big_rec2`
proof of `leq_card_cover`:
```
Lemma leq_card_bigcup (I T : finType) (P : pred I) (F : I -> {set T}) :
  #|\bigcup_(i | P i) F i| <= \sum_(i | P i) #|F i|.
Proof.
elim/big_rec2: _ => [|i n U _ leUn]; first by rewrite cards0.
by rewrite (leq_trans (leq_card_setU (F i) U).1) ?leq_add2l.
Qed.
```

### 8. `#|A| <= 1` from "all elements equal"
Use `card_le1_eqP : reflect {in A &, forall x, all_equal_to x} (#|A| <= 1)`
(note: the conclusion is `y = x`, i.e. the **second** element on the left).
`card_le1P` is the `A =i pred1 x` variant and is usually the wrong one.

### 9. Rewriting under `<` with `bigD1`
To split both sides of `\sum … < \sum …` at index `i`:
```
rewrite /pot (bigD1 i) //= [X in _ < X](bigD1 i) //= -addSn.
apply: leq_add; …
```
`-addSn` turns `(A + B).+1` into `A.+1 + B` so that `leq_add` splits the
strict inequality into a strict head and a pointwise tail.

### 10. `[set x; y] = [set y; x]`
No `set2C` in mathcomp's `finset`; prove it once:
`by apply/setP => z; rewrite !inE orbC.`

### 11. Dividing both sides by Δ
Goal `#|E(G)| %/ Δ <= #|M|` from `#|E(G)| <= #|V| * Δ` and `#|V| = #|M|`:
`rewrite -defM -(mulnK #|V| dpos); apply: leq_div2r.`
i.e. turn the bare `#|V|` on the right into `#|V| * Δ %/ Δ` and use monotonicity
(`leq_div2r`), instead of hunting for a `leq_divLR`-style lemma whose exact
`+ d - 1` shape you have to guess.

## classical-lemmas (necklace / ℤ_p Tucker) — session 2

### 12. `mulrCA` / `mulrC` "does not match any subterm" on an obviously matching goal
The ring was declared `nzRingType` (non-commutative); `mulrC`, `mulrCA`, `mulrAC` need a
`comNzRingType`. Either declare `R : comNzRingType`, or use centrality of naturals:
`rewrite !mulrA; congr (_ * _)%R; rewrite mulr_natr mulr_natl` (`x * n%:R = x *+ n = n%:R * x`).

### 13. `/=` turns `2 * s.+1` into `(s + 1 * s.+1)%coq_nat`
`simpl` unfolds `muln 2 (S s)` through `Nat.mul`. Before simplifying a goal containing
`2 * s`, freeze it: `rewrite mulnS !addSn add0n; set n := 2 * s in IH *.` Then `/=`
(and `take n.+2 (x :: y :: l)` etc.) reduce cleanly with `n` opaque.

### 14. A `have` inside a file where `ring_scope` is NOT open
Write the whole statement under `( … )%R`, put `%N` on nat comparisons used as ring
elements (`(p <= x + y)%N%:R`) and pin the ring with `:> R`; otherwise Rocq generalises a
fresh `forall t : pzRingType` in front of the `have`.

### 15. `have h u v l : mergeat 0 (u :: v :: l) = … by [].` → "No applicable tactic"
Untyped binder `l` was not inferred as `seq nat`; annotate `(l : seq nat)`. Also
`drop 2 (u :: v :: l)` simplifies to `drop 0 l`, so finish with `rewrite /mergeat /= drop0`.

### 16. Name clash: `merge` is mathcomp's merge-sort (`path.v`)
A local `Definition merge` shadows it, but later `merge i.+2 …` was parsed against the
library one after a global rename — pick a fresh name (`mergeat`). Beware blind
`replace("merge", …)` edits renaming lemma names too (`salt_merge_sum` became
`salt_mergeat_sum` and `open{theorem}` "not found").

### 17. Nested views in intro patterns: `/and3P [xp yp /andP [zp alla]]`
Fails with "Illegal application: andP ?i" when the branch hypothesis is `true` (the
size-2 case had `all _ [::]`). Split the destructuring across goals, or discharge the
degenerate case first (`by move: sz; rewrite mulnS !addSn add0n.`).

### 18. `rewrite [behead _]/=` "partial term does not match"
Use `have -> : behead [:: x, y, z & a] = [:: y, z & a] by [].` instead of pattern-`/=`.

### 19. Lifting `big_ord_recl` indices
After `2!big_ord_recl` the body has `lift ord0 (lift ord0 i)`; inside `eq_bigr` use
`rewrite !lift0` (`lift ord0 i = i.+1 :> nat`) before lemmas stated with `i.+2`.
Signs: `(-1)^+ i.+2 = (-1)^+ i` by `rewrite !exprS !mulN1r opprK`.

### 20. rocq-mcp-evolve notes
`build{file}` diagnoses all proofs and does NOT report `Admitted` as holes; `open{theorem}`
requires the exact lemma name; `try{candidates}` is the cheapest way to probe 3–4
rewrite chains at once (only the first success is committed).

## classical-lemmas Stage A (co-hemisphere cochains) — extra lessons

### 21. `signr_odd` rewrites the WRONG way for `(-1)^+ k.+1`
`signr_odd n : (-1)^+ (odd n) = ...`? No — it states `(-1) ^+ (odd n) = ...`.
To turn `(-1)^+ n.+1` (n even) into `-1`, use `-[( (-1) ^+ ord_max.+1)%R]signr_odd`
(note the leading `-` = rewrite right-to-left) then `/= oddn expr1 mulN1r`.

### 22. `-(lemma)` vs `-[RHS](lemma)` when the same term occurs on both sides
`rewrite -(count_shift0 R vp)` folded BOTH the RHS `1` and (spuriously) matched
inside the LHS summand, producing a stray `*+`. Restrict with `-[RHS](count_shift0 …)`.

### 23. `?leqW` inside a `rewrite` does NOT discharge a `_ < _.+1` side goal
`rewrite (Phi_evenE oddn) ?size_delete ?sz //` leaves the `size_delete`
side-condition `i.+1 < n.+2` as a SECOND goal of the `have`. Close it after the
main branch with a nested `exact: leqW hi` (indent the main branch under one `.`),
not by stuffing `?leqW` into the rewrite (it silently no-ops and the goal survives,
so the next `big_ord_recl` then fails on the wrong goal).

### 24. `under eq_bigr` needs the summand in the exact library shape
After `2!big_ord_recl` the residual sum body has `lift ord0 (lift ord0 i)` /
`bump 0 (bump 0 i)`; inside `under eq_bigr => i _ do rewrite -[bump 0 (bump 0 i)]/(i.+2) …`
to normalise the index before applying `i.+2`-stated lemmas.

### 25. Evaluating HSSZ cochains at the neutral element = a boolean value model
Rather than build ℤ_p[ℤ_p]-chains, model `φ_d` directly as a `bool`-valued
function `Phi d` of the vertex residue sequence (`salt` + a `dmod` guard). The
group-ring Stokes identities (Prop 3.8) then reduce to two finite boolean/nat
identities (`salt_merge_sum`, `sigma_count`) — far cheaper than the resolution
algebra, and provably the same numbers.

## classical-lemmas Stage B — cubical chain complex (cubical.v)

### 26. `∂∂ = 0` over ANY ring without the 2Σ=0 trap
The naive `\sum_i\sum_j F = \sum_i\sum_j F(swap) = -\sum` gives only `2Σ=0` (fails char 2).
Correct ring-general pairing (`sum_pair_anti`): `rewrite pair_big`, `bigID (val q.2<val q.1)`,
`reindex_inj` by the swap `(q.2,q.1)` on the second half, `eq_bigr` to flip the summand via
antisymmetry, then reconcile the two halves' predicates through the diagonal
(`big_mkcond`+`eq_bigr`+`ltngtP`, using `F i i = 0` on `val i = val j`).

### 27. Modelling R^N cells as `{ffun 'I_N -> cell1}`
`cell1 := (cut + ('I_n*'I_p))%type` (a finType for free) avoids inductive-eqType boilerplate;
`Vtx`/`Edg` are `inl`/`inr`. Faces `fv c j v := [ffun i => if i==j then Vtx v else c i]`.
Key calculus lemmas: `fvC` (commute distinct coords), `is_edge_fv`, `rk_fv`
(rank drops by `(val j < val i)` when coordinate j is turned into a vertex).

### 28. Boundary as `lin bd1` and `bd∘bd`
Define `bd := lin bd1` (chains.v). `bd (bd x) = 0` reduces via `lin_comp` + `big1` to
`bd (bd1 c) = 0` for each basis cell; fold the unfolded `\sum_x0 (bd1 c) x0 *: bd1 x0` back to
`bd (bd1 c)` with `-/(lin bd1 (bd1 c)) -/(bd (bd1 c))` before applying the per-cell fact.

### 29. Scope traps under `Local Open Scope ring_scope`
`val i < val j` and `rk c i - (b:bool)` get parsed in ring/order scope — always write the nat
`< `/`-` under `%N` in statements (`(rk c i - (val j < val i))%N`). An unused section-lemma
binder (`fv_id c j v k w` with `k w` unused) yields "Cannot infer the type" — drop it or annotate.

### 30. `~~ true` / `~~ false` in `[&& _,_ & _]` conditions
`rewrite eqxx` will NOT fire on `j != j`; use `case: ifP` or reduce with `!andbF` (both branches)
then `oppr0`. `case: (boolP b)` does not substitute `b` in the goal — use `case E : b` to get a
rewritable equation `b = true/false`.

## classical-lemmas Stage B complete — hemisphere chains (hemispheres.v)

### 31. Reusing section-generalised defs downstream: add `Arguments`
`cubical.v` closed its section, so `bd1 n p N R c` etc. had all params explicit and
broke every downstream use. Fix: after `End Section`, `Arguments bd1 {n p N R} c.`
(and `Arguments cellN : clear implicits.` for the type). Do this in the DEFINING file.

### 32. `cc`/`lin` chains: pin the ring with an ascription
`Definition nu := lin (fun c => cc (shift c))` fails ("shift c expected comNzRingType")
because `cc`'s `{R}` is unconstrained. Ascribe the lambda body: `lin (fun c : cellN => cc (shift c) : chain)`.

### 33. `have`/`Lemma` inside a section re-generalises an ambiguous ring as a fresh `t`
A `have Hj : \sum ... = cc ... - cc ...` sprouted a spurious `forall t : comNzRingType`.
Pin the equation's ring with `:> chain` (here `chain := {ffun cell -> R^o}`).

### 34. `case: (boolP b)` does not substitute; `contraTneq` needs a bool goal
For `j' != j` from `c j' = Vtx(Some..)` and `c j = Vtx None`, don't use `contraTneq`
(the goal is an inequality, not `is_true`): `apply/eqP => e; move: hj'; rewrite e cj`.

### 35. Relabelling-chain support: one reusable lemma
`lin_cc_supp : (lin (fun c => cc (g c)) X) d != 0 -> exists2 c, X c != 0 & g c = d`
(proof: `boolP [exists c, (X c != 0) && (g c == d)]`, else the sum is `big1`). This
powers every `coveredX_*` / `below_*` lemma for ν, σ, topcoord, consP in one line each.

### 36. Front-factor cubical boundary law `bd_placeP1` (Lemma 2.3 for P_1)
`below j x -> bd (consP j x) = topcoord j x - x - consP j (bd x)`. Structure that worked:
per-cell (`bd_placeP1_cell`) then linearity assembly via `big_morph (consP j)` /
`big_morph bd` and `-!sumrB`. Per-cell: split `bd1(setc c j (Edg k))` at `j` with `bigD1 j`;
the j-edge terms telescope (`edge_telescope`, reused from `bd_P1`), the `i>j` terms give
`-consP j (bd1 c)` using `rk_setc_below` (rank rises by 1) + `fv_setc_comm` + `exprS mulN1r`.

### 37. Hemisphere relations need only ∂∂=0, ν a chain map, and (ν−id)∘Σ=0
With the uniform `h d := bd (consP (pc d) (htil d)) + htil d`, `∂h_{d+1} = op_d(h_d)`
follows from `bd_bd`, `bd_nu`/`bd_sigma`, and `opd_kills_htil` (from `nusigma`/`sigma_nuid`,
and `sigma (cc o_cell) = 0` in char p). The front-factor law is needed ONLY for the
`h_d ∈ C(K)` claim (via the alternative form `h_d = topcoord - consP(∂h̃_d)` and a coverage
induction `bd_htil_covered`).

## classical-lemmas Stage C — induced chain map (simplotope.v, chainmap.v)

### 38. rocq-mcp: `check` restarts the proof, `step` is incremental
`mcp__rocq__check` re-runs the whole script from `Proof.`; feeding it a continuation
of an already-committed proof silently rolls back to the statement. Use `step` (and
`try` for several candidates) when repairing a proof in the middle.

### 39. `rewrite -h` with `h : X = 0` also rewrites a big operator's identity element
`rewrite -hz` on `\sum_q F q = 0` turned the goal into `\big[+%R/(the RHS of hz)]_q ...`.
Always target the side: `rewrite -[RHS]hz`. Same trap for `have -> : (0 : R) = f rho`.

### 40. `pair_bigA` is unusable right-to-left (higher-order pattern)
`rewrite -pair_bigA` fails on `\sum_(q : I*I) F q.1 q.2` ("does not match"). Instead
state the iterated form in a `have -> : <pair form> = <iterated form> by rewrite pair_bigA.`
so the rewrite runs left-to-right on the explicit iterated sum.

### 41. A section ring that no explicit argument mentions stays explicit after `End`
`Lbd1_coef : Lvalid s iv -> Lbd1 s (Lfacet ..) = (-1)^+(Lsign s iv)` keeps `R` explicit
(nothing determines it). Downstream call it as `@Lbd1_coef t p R s iv hiv`.
Symmetrically `muP` (proved by `elim=> [|d IH] c ...`) keeps `d` and `c` explicit:
`@muP (dimS c) c okc (erefl (dimS c))`.

### 42. Annotate binder types when a `forall` precedes the boolean that fixes them
`Lemma LsubP s s' : reflect (forall i, s i \subset s' i) (Lsub s s')` fails to elaborate
(`s` gets a bogus dependent type). Write `Lemma LsubP (s s' : Lcell) : ...`.

### 43. `case: ifP => // h; rewrite ...` applies the rewrite to ALL remaining goals
The `//` does not close `0 x = 0` (needs `ffunE`), and the chained `rewrite scale_ffunE`
then fails on that goal. Use `case: ifP => h; last by rewrite ffunE.`

### 44. `eqVneq` already simplifies the comparison in the goal
`case: (eqVneq x v) => [->|xv]` leaves `(true || ...) && ...`; a following `rewrite eqxx`
fails. Just continue with `ltnn`/`andbF`/`(negbTE ...)`.

### 45. Do not rewrite a section nat `p` inside a goal mentioning `'I_p`
`rewrite -(ltn_predK p_gt0)` on `(val x).+1 < p` gives "Dependent type error" because
`nat_of_ord` mentions `p`. Use transitivity instead:
`apply: (leq_ltn_trans (ltn_taup h)); rewrite ltn_predL.`

### 46. `injective f` has EXPLICIT `x1 x2`; the `/f_inj` view can fail
After `move=> [a x] [b y] /= [e1 e2]` the second component is an equality of `val`s,
not of `f`-images, so `/shp_inj` is ill-typed. Rebuild the goal instead:
`congr pair; apply: shp_inj; apply/val_inj; exact: e2.`

### 47. `lin_comp` needs `lin g (lin f c)` syntactically
Unfold the abbreviations first (`rewrite /Lbd /mu /Lnu lin_comp`), otherwise the
`lin _ (lin _ _)` pattern is not found.

### 48. Filtered sums need their own linearity lemma
`lin_sum` is stated for `\sum_(i <- r) F i` and does not match `\sum_(i | P i) F i`.
Added `lin_sum_cond` (proof: `big_mkcond; lin_sum; [RHS]big_mkcond; eq_bigr`).

### 49. `exact: h` can fail where `by rewrite h` succeeds
On a boolean equation that is syntactically the goal (`odd (...) = odd (...)`),
`exact:`/`apply:` reported "Cannot apply lemma"; `by rewrite h` closed it.

### 50. Theorem 2.4 (chain map) — the shape that worked
Recurse on the DIMENSION, not on the cell: `Fixpoint mf d c` with
`mf d.+1 c = alphaOf (msp c) (lin (mf d) (bdS1 c)) *: cc (msp c)`, then
`mu1 c := mf (dimS c) c`. The induction proves the pair
`(mu1 c != 0 -> Ldim (msp c) = dimS c) /\ Lbd (mu1 c) = mu (bdS1 c)`.
Three cases on `Ldim (msp c)` vs `dimS c = d.+1`: `< d` (every facet contributes 0),
`= d` (the image chain is a multiple of `cc (msp c)`, killed by `∂` when `d ≥ 1` and by
the AUGMENTATION `\sum_f bdS1 c f = 0` when `d = 0`), `= d.+1` (the real case:
`Lfacet_ker2`, resp. `Lfacet_ker1` in dimension 1).

### 51. Lemma 2.1 (facet-graph connectivity) is cheaper at the level of coefficients
No graph needed: prove `gam iv = gam jw` whenever `(iv,jw)` is an admissible DOUBLE
facet (from `double_facet_uniq` + `Lsign_anti`, evaluating `∂∂ = 0` at that double facet),
then the three cases of Lemma 2.1 (different factors / same factor with `|σ_i| ≥ 3` /
same factor with `|σ_i| = 2`, bridged by a third factor supplied by `Ldim σ ≥ 2`).

### 52. ℤ_p-equivariance on `(Δ_{p-1})^t` costs one parity identity
The shift is NOT orientation preserving: the induced chain map is
`Lnu1 s = (-1)^+(esgn s) *: cc (Lsh s)` with `esgn s = Σ_i (if τ ∈ s_i then |s_i|-1 else 0)`,
`τ = p-1`. `∂ ∘ Lnu = Lnu ∘ ∂` reduces (reindex by `(i,v) ↦ (i, shp v)`) to
`odd (eA A + rk (σA) (σv)) = odd (rk A v + eA (A :\ v))`, proved by three cases on
`v = τ` / `τ ∈ A` / `τ ∉ A`. Convert exponents with `signr_odd`.

### 53. Equivariance of the induced chain map needs no new induction machinery
`mu1 (nuS c) = Lnu (mu1 c)`: both sides are multiples of `cc (Lsh (msp c))`, and
`∂` of the two sides agree (by the chain-map property plus the IH on facets), so the two
scalars are equal as soon as `Ldim (Lsh (msp c)) ≥ 1`; when it is 0 both sides vanish by
`mu_dim`.

## classical-lemmas Stage D — the bar complex (bar.v)

### 54. Bounded sequences as a finType: pad into a tuple, work on the sequences
`cellB := M.-tuple (option 'I_p)` with `padd : seq 'I_p -> cellB` (map Some, pad
with None, `insubd`) and `sqB := pmap id`.  `sq_padd : size s <= M -> sqB (padd s) = s`
is the only bridge needed: it makes `padd` injective, and EVERY operation
(boundary, action, contraction) is defined by `padd (f (sqB c))`, so all the
combinatorics happens on plain sequences with mathcomp's `take`/`drop` lemmas.
No index shifting inside `'I_M` anywhere.

### 55. ∂∂ = 0 for a simplicial complex: a sign-reversing involution
`sum_invol` (in `chains.v`): `\sum_(i | P i) F i = 0` from an involution `tau` of
`P` with `F (tau i) = - F i` and `tau i != i`.  Proof: `bigID` on
`enum_rank i < enum_rank (tau i)` then `reindex_inj` of one half onto the other —
char-2 safe, unlike "2Σ = 0".  For the bar complex take
`tau (i,j) = if j < i then (j, i-1) else (j+1, i)` on `'I_M * 'I_M`; the two cells
agree by the simplicial identity `dels j (dels i s) = dels i (dels j.+1 s)` (i ≤ j).

### 56. Ordinal arithmetic inside an involution: go through a total `iM`
`iM k := insubd (Ordinal M_gt0) k` with `val_iM : k < M -> val (iM k) = k` and
`iM_val : iM (val i) = i` keeps `tau` total (needed: `sum_invol` wants a global
function) while the four side conditions are proved under `P`, where all the
bounds hold.

### 57. `case: ifP` splits the OUTER `if`
Proving `tau (tau q) = q` by `case: ifP` split the if of `tau (tau q)`, not the
inner one.  Use `case hxy : (val q.2 < val q.1)%N => /=` to force the inner test.

### 58. `big_ord_widen` moves between `\sum_(i < n)` and `\sum_(i < M | i < n)`
Needed to peel off the first term of a bar boundary (`big_ord_recl`, with
`val (lift ord0 i) = i.+1` via `/bump /=`) while keeping a uniform `'I_M` index.

### 59. `%%` parses in `ring_scope` under `Local Open Scope ring_scope`
`val (iter r shp x) = (val x + r) %% p` elaborated `%%` as polynomial division.
Annotate the whole equation with `%N`.

### 60. Choosing the target of η_#: contractible beats (N-2)-connected
Meunier's `ℤ_p^{*N}` needs barycentric subdivision and a connectivity argument to
build `η_#`.  The homogeneous bar resolution `EℤZ_p` carries the same cochains
(HSSZ's `f_d`, `u` — and our `salt.v` is literally stated on value sequences with
`delete i` as faces) and is contractible, so the equivariant lift is a plain
induction.  The rest of the proof of Theorem 3.3 is unchanged.

## classical-lemmas Stage D finished — cochains and η_# (bar.v, eta.v)

### 61. Lifting `salt.v`'s sequence identities to cochains costs almost nothing
`phi d x := Σ_c x c * (Phi p d (natseq c))%:R` is additive and homogeneous, so the
chain identities follow from the per-cell ones by `phi_lin`; and the per-cell ones
are the `salt.v` lemmas verbatim when the size matches, both sides being 0
otherwise (`Phi_size`). The size bookkeeping is `size_dels` + `big_ord_widen`.

### 62. `exchange_big` after unfolding `phi` scrambles the pairing
Proving `φ_{2l+1} ∘ ∂ = φ_{2l+2} ∘ Σν^r`, exchanging first put the CELL sum
outside and left a goal comparing coefficients, which is false termwise. Rewrite
the right-hand side with `iter_nuB_lin` and `phi_lin` FIRST, so both sides are
`Σ_cell x c * (…)`, and only then `exchange_big`.

### 63. A free ℤ_p-action needs p prime, and the proof is the pigeonhole
`Lshk k s = s` with `0 < k < p` forces every factor of `s` to be invariant under
`shp^k`; with `p` prime, `m ↦ (a + k*m) %% p` is injective on `'I_p`
(`Euclid_dvdM` + `eqn_mod_dvd`), hence surjective (`inj_card_bij`), so a nonempty
invariant factor is everything, i.e. `s` is the top simplotope.

### 64. Orbit representatives: `[arg min_(k < i0) enum_rank (Lshk k s)]`
`repL_shk : repL (Lshk k s) = repL s` needs no uniqueness-of-argmin reasoning:
each of `repL s`, `repL (Lshk k s)` lies in the other's orbit, so `repL_min` gives
both inequalities on `enum_rank` and `enum_rank_inj` finishes.

### 65. The ℤ_p action on C(L) carries signs, so equivariance is twisted
`Lnu1 s = (-1)^{esgn s} ⋅ (Lsh s)`, so propagating `η_#` along an orbit multiplies
by `Esg j r = Σ_{i<j} esgn (Lsh^i r)`. Consistency at the wrap-around is exactly
`Esg_p_even`, proved by `Σ_{i<p} eA (σ^i A) = |A| * (|A| - 1)` — count the `i` with
`τ ∈ σ^i A` by the unique `i` sending each `a ∈ A` to `τ`. The same fact is what
makes `Lnu^p = id`.

### 66. Contractible target ⇒ the induction needs only `∂ D + D ∂ = id`
`bdB_DB_hom` is stated exactly in the shape the induction consumes: a homogeneous,
normalised cycle of dimension `k-1`, plus a vanishing augmentation when `k = 1`
(supplied by `Lbd1_aug`, the augmentation of the boundary of a 1-simplotope).
Carry "normalised and of size `d+1`" (`okB`) as an unconditional induction on the
recursion depth — it never needs `okL` or `Ldim`.

### 67. Section-closed constants: pass the section hypothesis, or use `@`
After `End`, `Lshk`, `repL`, `esgn`, `nuB`, `DB` all take their `0 < p` hypothesis
as an argument. Writing the follow-up development INSIDE the same section (a nested
`Section EtaRing` with `Variable R`) avoids re-threading every one of them.

### 68. `Set Implicit Arguments` makes a lemma's *binders* implicit even when they
### look like plain parameters — and even under a leading `forall`
`Lemma stepB l : ((2 * l).+2 < D)%N -> ... ` closes as `stepB [l] _ _`, and so does
`Lemma indA : forall l, (2 * l < D)%N -> ...` (`indA [l] _`). So `apply: (stepB l hl)`
fails with `Cannot apply lemma (stepB hl)` — the `l` was eaten as the proof argument.
Fix: always write `@stepB l hl` / `@indA l hlt` for in-file lemmas whose first
argument is a `nat` index. `About <lemma>.` inserted temporarily in the file is the
fastest way to see the real arity.

### 69. `move: h; rewrite e => h` rewrites the CONCLUSION too
`move: hl; rewrite he => hl` with `he : 2 * l.+1 = (2 * l).+2` also turned the goal
`Psi (2 * l.+1) ... = 1` into `Psi (2 * l).+2 ... = 1`, after which `apply:` of a
lemma stated with `2 * l.+1` fails (ssreflect's keyed matching does not see through
the conversion). Fix: derive the reshaped hypothesis separately,
`have hl2 : ((2 * l).+2 < D)%N by rewrite -he.`, leaving the goal untouched.

### 70. `set x := pat` needs the pattern to OCCUR in the goal
`set c0 := setc _ _ _.` after a `have hc0 : hK 0 = cc (setc ...)` fails with
"The pattern (setc _ _ _) did not match and has holes" — the goal never mentions
`setc`. When all you want is an opaque name for the cell, package it:
`have [c0 hc0] : exists c0 : cN, hK 0 = cc c0 by exists (setc ...); exact: h0_val.`

### 71. `2 * l.+1 = (2 * l).+2`
`by rewrite mulnSr addn2.` (`mulnSr : m * n.+1 = m * n + m`). The variant
`mulnS addnC -addn2 addnA` fails ("No applicable tactic": `-addn2` has nothing to
match). For `(2*l).+1 < NN` from `(2*l).+1 < D` with `NN = D.+1`:
`by rewrite /NN ltnS ltnW.` — `rewrite ltnW` is legitimate: its conclusion is a
boolean, so it rewrites the goal to `true` and leaves the strict inequality as a
side goal that `by`'s `done` discharges by assumption.

### 72. Extracting a support cell from `x != 0`
There is no `chain_neq0` in mathcomp; the two-line proof is
```coq
move=> hx; apply/existsP; rewrite -[X in is_true X]negbK; apply/negP => /existsPn h.
move/eqP: hx; apply; apply/ffunP => c; rewrite ffunE.
by move: (h c); rewrite negbK => /eqP.
```
(`ffunE` does simplify `(0 : {ffun _ -> R^o}) c`.)

### 73. `apply/negP => /lemma` without a name is not a tactic
`apply/negP => /eta.okL_Ldim; rewrite ...` gives "No applicable tactic": a view on
an intro pattern must be followed by a name (or `_`). Write
`apply/negP => hok; move: (eta.okL_Ldim p_gt0 hok); rewrite ...` instead. Note also
that `okL_Ldim` keeps `0 < p` as an EXPLICIT argument after the section closes.

### 74. Instantiating the ring at the very end: `'F_p`
```coq
pose Rp : comNzRingType := 'F_p.
have pR : (p%:R = 0 :> Rp) by apply: pcharf0; exact: pchar_Fp.
```
(`char_Fp`/`charf0` are the deprecated spellings since mathcomp 2.4.) `'F_p` is a
`comNzRingType` by canonical structure, but only `pose ... : comNzRingType := 'F_p`
makes it usable in an explicit `@lemma ... R ...` position.

## classical-lemmas finished — the Splitting Necklace Theorem (necklace_prime.v, necklace.v)

### 75. `xchoose` needs a BOOLEAN predicate; for a `Prop` use `fin_all_exists`
`pose b r := xchoose (hb r)` with `hb r : exists b : seq 'I_q2, [/\ … ]` fails
("expected `exists x : Datatypes_list__canonical__choice_Choice …`") because
`xchoose {T : choiceType} {P : pred T}` only takes a *boolean* `P`. When the
index ranges over a finType, `fin_all_exists` does the job with no choice axiom:
`have [b hbP] := fin_all_exists hb.`  (`hb : forall r : 'I_q1, exists u, P r u`.)

### 76. Rewriting `p` when `p` is also an index of a type in the goal
`rewrite -(hWp i)` / `rewrite n0` fail with "Dependent type error … `{set 'I_p}`
should be a subtype of `set_type 'I__pattern_value_`" as soon as the goal
mentions `'I_p` (or `pred 'I_n`). Two escapes:
  - bound the cardinal instead of computing it:
    `apply/eqP; rewrite -leqn0; apply: leq_trans (max_card A) _; rewrite card_ord n0.`
  - move the equation the other way: derive `hh : (#|A :\ x|).+1 = p` by rewriting
    *inside a hypothesis*, then `apply: succn_inj; rewrite hh …` — never rewrite `p`
    in the goal.

### 77. The first coordinate covering a bead: `find` on `enum 'I_N`
`jw v b := nth j0 (enum 'I_NN) (find (fun j => covers (v j) b) (enum 'I_NN))` is a
TOTAL "smallest index such that …" (no `arg min` witness needed). Its two
characteristic lemmas come from `nth_find` and `before_find`, using
`nth_ord_enum : nth i0 (enum 'I_n) i = i` and `has_find`/`size_enum_ord` to turn
`find … < N` into an ordinal. `eq_find` then gives `jw v b = jw v' b` from
pointwise equality of the predicates.

### 78. Packing a lexicographic tie-break into one number
Meunier's `i`-winner is "most `i`-beads, ties broken by the rightmost one".
Encoding it as `sc v i r = cnt v i r * n.+1 + rk v i r` with `rk ≤ n` makes
`[arg max_(r > r0) sc v i r]` the right notion, and both components are recovered
by `divnMDl` / `modnMDl` (`divn_small`, `modn_small` for the remainder), which is
what proves uniqueness of the maximiser — and uniqueness is what makes the map
equivariant (`arg max` alone is not).

### 79. `#|A| ≤ #|B| + 1` by an injection into `B` off one point
`rewrite (cardsD1 x A) -add1n; apply: leq_add; first exact: leq_b1.`
then `rewrite -(card_in_imset hinj); exact: subset_leq_card hsub` with
`hinj : {in A :\ x &, injective f}` and `hsub : [set f y | y in A :\ x] \subset B`.

### 80. Double counting a partition: `exchange_big_dep`
`\sum_(b | c b == i) #|Sb b| = #|Si i|` is `-sum1_card`, `eq_bigr` to a double
sum, then
`rewrite (exchange_big_dep (fun j => j \in Si i)) /=` (the side condition is
"`c b = i` and `j ∈ Sb b` imply `j ∈ Si i`"), and finally `big_pred1 (bdo (u j))`
for the inner sum. The same three lines give `\sum_i di i = #|S|` and
`\sum_r cnt v i r = #|[set b | c b == i]|`.

### 81. `#|[set pr : 'I_n * 'I_n | …]|` versus a count over `iota`
To identify the two readings of "number of cuts":
`rewrite /cuts -sum1dep_card -(pair_big_dep xpredT Q (fun _ _ => 1))` turns the
cardinal into `\sum_i \sum_j`, and `eq_bigl` + `big_pred1` evaluates the inner
sum. On the sequence side, `sum_count` (`count P s = \sum_(x <- s) (P x : nat)`)
plus `big_mkord` lands on the same `\sum_(i < n)`. `rewrite /index_iota subn0` is
needed to see `iota 0 n` as the range of `\sum_(0 <= m < n)`.

### 82. A type that occurs nowhere breaks equivariance
No equivariant `λ_i` can be simplotopal when type `i` has no bead (`d_i = 0`
forces `λ_i` constant on every face, but equivariance forbids a constant). So
the prime case is proved under "every type occurs" and the general statement is
recovered by relabelling with `enum_rank_in` / `enum_val` on
`P := [set k | [exists b, c b == k]]` (`enum_rankK_in`, `enum_valK_in`,
`max_card` for `#|P| ≤ t`).

### 83. `nth_map` wants its index bound explicitly
`rewrite !(nth_map i0) ?size_enum_ord //` silently fails ("No applicable
tactic") when the two occurrences need different bounds. Name them:
`rewrite (nth_map i0 (a i0) a (s := enum 'I_n) (n := m)) ?size_enum_ord ?(ltnW hm) //.`

## X15: König line colouring, Carathéodory, necklace interpolation (16 Sept 2026)

### 84. A directory reorganisation invalidates the MCP project configuration
After `git mv`-ing `classical-lemmas/theories/*.v` into `necklace/`, `konig/`
and `caratheodory/`, `mcp__rocq__open` could no longer resolve **any**
`ClassicalLemmas.*` module (and, oddly, none of `packing-theory` either): the
server keeps one cached, flat project configuration, and it also wants `.vos`
files. `make -f Makefile.coq vos` fixes the second half; the first needs a
server restart. Workaround used for this whole phase: a two-line harness that
feeds the file prefix (up to a marker line) plus a tactic script to
`rocq repl -q -R theories ClassicalLemmas` and prints the goals, with
`rocq c ...` for the real compile.

### 85. `mcp__rocq__check` does not remember the steps already committed
It re-checks from `Proof.`, so a proof must be passed whole — from `Proof.` to
`Qed.` — not as the remaining fragment.

### 86. `rewrite !inE` over-unfolds definitions of `{set}`
On a goal mentioning `SS`, `Tsel`, `Csel` (definitions that are themselves
`[set …]`), `!inE` unfolds them into their defining boolean, and the goal
becomes unreadable and unmatched by later rewrites. Fix: prove one *view*
lemma per definition (`SSP`, `TselP`, `memsetP`, `mem_Csel`, `mergeP`) and use
`case/SSP` / `apply/TselP` instead of `inE`.

### 87. `congr (#|_|)` does not leave a set equality
Cardinal goals `#|A| = #|B|` are better closed by `have -> : A = B` (then
`apply/setP => x; rewrite !inE …`) than by `congr`, which leaves a goal about
the `finset` structure that `setP` cannot attack directly.

### 88. `setIidPr` is a `reflect`, not an equation
`rewrite setIidPr` fails; use `have -> : E(G) :&: cls j = cls j by apply/setIidPr; exact: cls_sub.`

### 89. `apply: (leq_trans (_ : X <= _))` picks the wrong side
`leq_trans : m <= n -> n <= p -> m <= p`. To insert `X` as the *middle* term,
the annotation must constrain the conclusion of the first argument:
`apply: (leq_trans (_ : _ <= X))`, not `(_ : X <= _)`.

### 90. Names that moved in mathcomp 2.5
`leq_trunc_div` is deprecated for `leq_divM`; `sum_nat_eq0` is the `finType`
version and `sum_nat_seq_eq0` the `seq` one; `leq_divRL`/`ltn_divLR` need
`0 < d` as a *hypothesis argument*, while `leq_divLR` needs `d %| m`.

### 91. `\sum_(i <- enum T | P i)` is not syntactically `\sum_(i | P i)`
A sum produced by `big_map`/`big_filter` from `[seq … | j <- enum 'I_D & …]`
ranges over `enum 'I_D`; `rewrite big_enum_cond` turns it into the indexed form
`\sum_(j | P j)`, after which `bigID` and `big1` apply. The idiom that worked
throughout:
`rewrite big_map big_filter big_enum_cond /= [RHS](bigID P) /= [X in _ + X]big1 ?addn0`.

### 92. `lia` on ssrnat goals: convert the *hypotheses* too, and leave `leq`
`rewrite -!plusE -!multE -!minusE` must be applied `in h *`, not only in the
goal, or `lia` answers "Cannot find witness" for want of the hypotheses. And
mathcomp's `m <= n` is `m - n == 0`: `lia` does not see it, so finish with
`rewrite -!plusE -!multE; apply/leP; lia.` Nonlinear goals need `nia` with the
products already introduced as hypotheses, or a hand-proved identity
(`key_id`, `hE_arith`) — this is where most of the arithmetic time went.

### 93. Rational bookkeeping invites `mulrDl` to expand `2%:R` into `1+1`
The interpolation error was first carried in `rat`; every `2%:R` was silently
rewritten to `1+1` by ring lemmas and the invariants stopped matching. Fix:
carry everything scaled by the denominator, as natural numbers
(`realisesN d C Y V E` = `Y <= d*#|C| + E` and `d*#|C :&: W i| <= V i + E`),
and never leave `nat`.

### 94. An averaging recursion needs *two* error variables to have a fixed point
`mix_half` stated with one common error `E` for both inputs cannot be iterated:
the chain of halvings needs `(EA + EB)/2 + c`, i.e. the lemma must take `EA`
and `EB` separately. With that, `e <= e/2 + c` has the fixed point `2c` and the
dyadic chain costs at most twice one halving whatever the number of bits.

### 95. Implicit arguments created by *unfolding* a `Definition`
`x15_approx_fair m B` unfolds to `forall G E, … -> exists C, …`, so a lemma
whose conclusion is `x15_approx_fair m B'` gets `G` and `E` as implicit
arguments; `apply:`/`exact:` of such a lemma against the goal
`x15_approx_fair m B'` then fails with "Cannot apply lemma". Fix: introduce
`G`, `E` and the hypotheses first (`=> m G E bipG dpos famE`) and apply the
lemma fully, with `@` if needed.

### 96. `#|[set t | P t]| = count P (enum T)`
`rewrite cardsE cardE /enum_mem -enumT size_filter filter_predT` — useful to
bound the size of a `[seq … | j <- enum T & P j]` by the cardinal of the
support of a Carathéodory solution.

### 97. Computing with `unlift`
`zstat j l := if unlift ord0 l is Some i then … else …` is evaluated by
`rewrite unlift_none` at `ord0` and by `rewrite liftK` at `lift ord0 i`,
followed by `/=` to fire the iota-reduction of the `if`.

### 98. "Inconsistent assumptions over library …"
A stale `.vo` of a dependency after editing it; rebuild the whole dependency
package (`make classical-lemmas`) rather than the single file.

### 99. Section variables come back in declaration order, not where you left them
After `End Section`, a lemma proved inside it takes the section variables it
uses as *leading* arguments, in declaration order, so a call that worked inside
the section fails outside: `Chalf_matching bipf mA mB` becomes
`Chalf_matching m bipf mA mB`, `SA_A hs` becomes `@SA_A _ _ _ _ hs`. `Check
@lemma.` before guessing; the error usually reads "The term X has type T while
it is expected to have type U" with U the type of the *first* discharged
variable.

### 100. Which discharged variables stay explicit
With `Set Implicit Arguments`, a section variable becomes implicit only if it
occurs in the type of a *later explicit* argument. A family `W : 'I_m -> …`
that occurs only in the conclusion stays explicit while `m` (occurring in
`W`'s type) becomes implicit — so `rounds_exists E bipf hsize hmatch`, with `L`
and `s` also implicit because they are determined by `hsize : size s = 2 ^ L`.

### 101. `rewrite mulnDr` fires on the wrong `+`
In a goal like `2^L * #|C| + (2^L-1) * (16*m+24) <= P * (#|C| + K)`, `mulnDr`
matches `(2^L-1) * (16*m+24)` first, because `16*m+24` *is* an addition. Either
target the occurrence (`rewrite [X in _ <= X]mulnDr`) or fold the numerals into
local definitions beforehand: `pose K := 16*m+24` then `rewrite -/P -/K in hC2`.

### 102. Folding a `pose`d abbreviation into a hypothesis obtained later
`pose K := …` does not fold the occurrences of `…` in hypotheses created
afterwards (e.g. by `have [C [h1 h2 h3]] := thm …`). `rewrite -/P -/K in h2`
right after the `have` keeps the rest of the script readable and makes
`leq_add2l`, `leq_mul2r`, … match syntactically.

### 103. `a + b - 1 >= a` when `0 < b`
`by rewrite -addnBA // leq_addr` (`addnBA : p <= n -> m + (n - p) = m + n - p`,
side condition `1 <= D` discharged by the `//`). The `-subn1 leq_subRL` route
fails: there is no `_.-1` in the goal.

### 104. `x^1 <= x^k`
`rewrite -{1}(expn1 x); apply: leq_pexp2l` (side goals `0 < x` and `1 <= k`).
`leq_exp2l` is the wrong lemma here: it needs `1 < x`, which fails at `x = 1`.

### 105. `X <= n * X` for `0 < n`
`apply: leq_pmull` — shorter and more robust than
`rewrite -[X in X <= _]mul1n leq_pmul2r`, whose side condition `0 < X` may not
be closed by `//` when `X` is a variable sum.

### 106. Deleting dead proofs mechanically
`.glob` gives, for a file `F.v`, one `prf`/`def` line per declaration and one
`R<pos>:<pos> <module> <> <name> <kind>` line per reference; the declarations
with no reference (excluding `var`) are the dead ones. Iterate to a fixpoint,
recompiling each round. **Only automate `Lemma`/`Theorem` blocks** (delete from
the declaration line to the next `Qed.`): a `Definition` has no `Qed`, so the
same script swallows every declaration up to the next proof and silently
destroys the file. Keep a copy before each round.

### 107. `splitPr` cannot split at a *definition*
`have [s1 [s2 ->]] := splitPr hb` rewrites the goal's occurrence of the list,
so it fails when that list is a definition (`blocks f A B`) rather than a
variable — nothing gets substituted. Build the decomposition by hand instead:
```coq
set i := index b (blocks f A B).
have hi : i < size (blocks f A B) by rewrite index_mem.
have hdec : blocks f A B = take i (blocks f A B) ++ b :: drop i.+1 (blocks f A B).
  by rewrite -{1}(cat_take_drop i (blocks f A B)) (drop_nth [::] hi) nth_index.
```
and then `rewrite /bl hdec flatten_cat` wherever you need it.

### 108. `iota 0 m.+1` reduces under `/=` and wrecks `count` goals
`/=` turns `iota 0 m.+1` into `0 :: iota 1 m`, so a lemma stated over
`iota 0 m.+1` no longer matches. Two uses of that:
* to *avoid* it, state the auxiliary lemma over `iota 0 m` and bridge with a
  monotonicity lemma (`count_iota_le`);
* to *exploit* it, `rewrite -[iota 0 m.+1]/(0 :: iota 1 m) /=` peels the head
  bead of a group off by conversion — that is how `rrmd j = rm (off + j*m.+1)
  || rrmdc j` and the "class positions only" count are proved.

### 109. `case: l h1` fails when another hypothesis mentions `l`
"`l` is used in hypothesis `hl2`" — `case:` must generalize *every* hypothesis
depending on `l`. When the case analysis was only there to turn `0 < l` into
`l != 0`, skip it: `rewrite -lt0n hl1 andbT` does the job with no destruction.

### 110. `ord0` elaborates to the wrong `'I_n.+1` in a `have` statement
`have h : (tix false ord0 == tix true ord0) = false by rewrite tixE.` fails with
"The LHS of tixE does not match any subterm of the goal": the two `ord0`s were
unified with a different index than the one `tixE` expects. Annotate the
offending argument — `tix false (@ord0 m) == tix true (@ord0 m)` — rather than
the whole statement.

### 111. `uniq_size_uniq` wants `s1 =i s2`, not `x \in s2 = x \in s1`
`uniq_size_uniq : uniq s1 -> s1 =i s2 -> uniq s2 = (size s2 == size s1)`.
Two traps: the direction of the extensional equality (state it as
`L =i [seq k <- enum T | k \in L]`), and the conclusion, which in this MathComp
version is an *equation between booleans*, not a conjunction — so
`have /andP[_ /eqP h] := …` fails with "Illegal application (Non-functional
construction)". Take it as `have h := …` and finish with
`apply/eqP; rewrite -h filter_uniq // enum_uniq`.

### 112. Counting the elements of `enum T` outside an explicit finite list
To get `size [seq k <- enum T | P k] = #|T| - n` when `~~ P` holds exactly on an
explicit `n`-element list `L`:
```coq
have h  := uniq_size_uniq hu (hmem : L =i [seq k <- enum T | k \in L]).
have hC := count_predC (fun k : T => k \in L) (enum T).
rewrite -!size_filter -cardE card_T hsz3 in hC.
rewrite (@eq_filter _ _ [predC L]); last by move=> k; rewrite /L /= !inE !negb_or.
by apply/eqP; rewrite -(eqn_add2l n) hC; apply/eqP; rewrite mulnS.
```
`-cardE` is what turns `size (enum T)` into `#|T|`; `[predC L]` (not
`predC (mem L)`) is the form `eq_filter` accepts.

### 113. Strengthening a lemma by restricting one of its terms
`rCr_card_ge` ended in `… + count (fun e => ~~ rkeepE e) es`; the sharper ledger
needed `… + count (fun e => P e && ~~ rkeepE e) es`. The proof goes through
unchanged *provided* the set it charges to is restricted the same way
(`[set e in SS A B | P e && ~~ rkeepE e]` instead of `rBad`) and the places that
used `e \notin rBad` re-derive it from `e \notin [set … | P e && ~~ rkeepE e]`
plus the `P e` already in hand. Inline the restricted set literally: a `pose`d
abbreviation blocks the `card_seq_count` rewrite that converts it to a `count`.

### 114. `mcp__rocq__build` before fixing anything
One `build` call reports *every* broken proof of a file at once (each failing
lemma is `Admitted` in-session so its dependents are still checked), instead of
the one-error-per-`rocq c` loop. After a wide refactor of a 2500-line file it
turned "121 blocks OK, 1 hole" into a single targeted `open{theorem: …}`.

## X15: refuting Conjecture 1.14 on `5 K_4` (19 Sept 2026)

File: `packing-theory/theories/applications/fair_matching_edge_partition_disproved.v`.
Pattern of the whole development: **all finite data lives on `nat`/`seq`, is
decided by `vm_compute`, and is bridged to `'I_n`/`{set _}` by one reflection
lemma**.

### 115. `vm_compute` cannot touch `#|_|`, `{set _}`, `[forall _]`, `bigop`
In MathComp 2.5 `card`, `Finite.enum`, `enum_mem`, `finset`/`pred_of_set`,
`[forall]`/`[exists]` and `bigop` are `HB.lock`ed: a closed goal about them
does **not** reduce (`vm_compute` leaves the locked constant in place). State
every computed fact over `iota 0 n` with `all`, `has`, `count`, `uniq`, `%/`,
`minn`/`maxn`, and explicit `seq (nat * nat)` membership; then bridge with

```coq
Lemma all_iotaP n (Q : nat -> bool) : all Q (iota 0 n) -> forall m, m < n -> Q m.
Proof. by move=> /allP h m hm; apply: h; rewrite mem_iota. Qed.
```

applied to ordinals through `ltn_ord`.  Six tables (degrees, class/edge
compatibility, class disjointness, block membership, the `K_4` bichromatic
table) cost 3 s of `vm_compute` in total this way.

### 116. `vm_compute` is call-by-value, so `==>` is *not* lazy
`b ==> X` is `implb b X`, an application: under `vm_compute` the big `X` is
evaluated even when `b` is false.  For the 144k-case `K_4` table that turned a
1 s check into an unusable one.  Write the guard as an inline `if`, which is a
`match` and therefore lazy in its branches:

```coq
if inC i a b then <the big conjunction> else true
```

and read it back with a one-line helper, since `rewrite h` + `/=` would also
unfold `iota` (cf. §108):

```coq
Lemma ifTb (b x : bool) : b -> (if b then x else true) -> x.
Proof. by case: b. Qed.
```

### 117. `all_iotaP ^~ h` feeds the proof to the *index* slot
With `Set Implicit Arguments`, `all_iotaP : all Q (iota 0 n) -> forall m, m < n -> Q m`
has `n`, `Q` **and `m`** implicit (`m` occurs in the type of `m < n`), so the
only explicit arguments are the two proofs.  `/(all_iotaP ^~ hc)` therefore
means `fun x => all_iotaP x hc` with `hc` in the `m` slot and fails with
`The term "hc" has type "is_true (c < 20)" while it is expected to have type "nat -> bool"`.
Chain with `have` instead: `have k2 := all_iotaP (all_iotaP k1 hc) hd.`

### 118. `disjointP` does not exist here; and `!inE` must be avoided on `[set … ]` definitions
`[disjoint A & B]` is best attacked by `rewrite -setI_eq0; apply/eqP; apply/setP => e`
and then `rewrite in_set0; apply/negbTE/negP; rewrite in_setI => /andP[…]`.
Use `in_setI`/`in_set0` **by name**: `!inE` unfolds the `[set e | … ]`
definitions of the classes into their defining booleans (cf. §86) and nothing
matches afterwards.

### 119. `#|[set i : 'I_n | P (val i)]| = count P (iota 0 n)`
```coq
by rewrite cardsE cardE /enum_mem -enumT size_filter -val_enum_ord count_map.
```
Dropping `/enum_mem -enumT` makes `size_filter` fail with "No applicable
tactic": `enum A` is `enum_mem (mem A)` and the filter is invisible until the
notation is unfolded.  This is the lemma that turns `Delta H <= 3` into a
`count` over `iota`, via `bigmax_leqP` and `N(x) = [set v | x -- v]`.

### 120. `card_le1_eqP` hands back its two membership goals in reverse order
`apply: hcard` on `e1 = e2` opens `e2 \in …` *first*.  Rather than a brittle
`[ … | … ]`, close both uniformly with optional rewrites:
`by apply: hcard; rewrite inE ?h1M ?h2M ?hv ?hv2.`

### 121. `apply: (lem (fun i => f i))` fails where `apply: (lem (bk := fun i : 'I_6 => f i))` works
Passing the higher-order argument positionally left the elaborator unifying
`?bk i` against the goal and it answered `Cannot apply lemma`.  Naming the
argument (or `@`-applying and annotating the binder type) fixes it:
`apply: (no_assignment (bk := fun i : 'I_6 => blk (val (pk i).1))).`

### 122. A *conditional* `set2_eqE` is enough, and much cheaper
The unconditional `([set a;b] == [set c;d]) = …` needs a 16-case bash.  Every
use in practice has `x' != y'` at hand (the two ends of an edge), and then
```coq
Lemma set2_cases (T : finType) (x y x' y' : T) :
  x' != y' -> [set x; y] = [set x'; y'] ->
  ((x' == x) && (y' == y)) || ((x' == y) && (y' == x)).
```
is four lines: put `x'` and `y'` in `[set x; y]`, `case/orP` twice, and use
`x' != y'` to kill the two diagonal cases.

### 123. `have h : <reduced form> := F c.` instead of `rewrite /def /=`
`F1 c0 : bk c0 \in blocks_of (val c0)` where `blocks_of` is a `nth` into a
literal list: `have h0 : bk c0 \in [:: 0; 3] := F1 c0.` type-checks by
conversion and avoids `rewrite /blocks_of /=`, which would also try to simplify
the surrounding `\in` and the abstract `bk`.  Same trick for destructuring a
computed conjunction: `have /andP[hxy hblk] : adj a b by apply: inC_adj …`.

### 124. Discharging a false table lookup without `/=`
`move: (F2 c1 c5 …); rewrite e1; vm_compute.` — `/=` would happily unfold the
table definition (`bich` is `has` on a literal list) *and* anything else in the
goal; `vm_compute` on the residual `bich 1 1 5 -> False` reduces it to
`false = true -> False`, which `by` closes by `discriminate`.

### 125. `x -- y :> G` is not a notation
`edge_rel` has no "at type" form.  Annotate the *arguments* instead:
`Lemma edge_H (x y : H) : (x -- y) = adj (val x) (val y). Proof. by rewrite /edge_rel. Qed.`
(`val x` for `x : H := SGraph adjr_sym adjr_irrefl` over `'I_20` elaborates
fine — `{set H}` and `{set 'I_20}` are convertible.)

### 126. `inord` literals and `vm_compute`
`inord` does not compute, so ordinal *literals* under `vm_compute` must be
`@Ordinal n m (erefl true)`.  But `inord` is perfectly usable where nothing is
computed — e.g. to turn a `seq (nat * nat)` of edges into a `seq {set H}` for a
cardinality bound — provided one has

```coq
Lemma oeq (a b : nat) : a < 20 -> b < 20 -> ((inord a : 'I_20) == inord b) = (a == b).
Proof. by move=> ha hb; rewrite -val_eqE /= !inordK. Qed.
```

Then `5 <= #|Ecl i|` is one `uniq_leq_size` (`leq_card_seq`) plus
`map_inj_in_uniq`, with injectivity reduced by `oeq` to a purely numeric check
over the five pairs of the class — one proof for all six classes instead of six
literal five-element sets.

### 127. `'K_1,` inside a binder is parsed as the complete BIPARTITE graph

`[exists y : 'K_1, P]` fails with
`Syntax error: 'in' or [term level 200] expected after [term level 200]`,
pointing at the *closing* bracket.  Cause: `sgraph.v` declares both
`Notation "''K_' n" := (complete n)` and `Notation "''K_' n , m" := (KB n m)`,
so the comma of the binder is swallowed as the separator of `'K_n,m`.
Fix: parenthesise the type — `[exists y : ('K_1), P]` (same for `{set 'K_3}`
followed by a comma, `fun x : ('K_n) => …`, etc.).  With a *variable* graph
`G : sgraph` the problem does not arise, which is why the bug only shows up on
concrete complete-graph instances.

### 128. `Set Implicit Arguments` silently makes a section graph implicit

```coq
Section DelEdgeSet.
Variables (G : sgraph) (F : {set {set G}}).
...
Definition del_edge_set : sgraph := SGraph del_es_sym del_es_irrefl.
End DelEdgeSet.
```
closes with `del_edge_set : forall [G : sgraph], {set {set G}} -> sgraph` —
`G` is inferable from `F`, so it became implicit and `del_edge_set G F` fails
with `The term "G" has type "sgraph" while it is expected to have type
"{set {set ?G0}}"`.  Add `Arguments del_edge_set : clear implicits.` right
after `End`, so statements read `del_edge_set G F`.

### 129. `[rel x y | …]` behind a `Definition` is not unfolded by `/=`

`move=> x y /=` leaves `del_es_rel x y = del_es_rel y x` untouched: `/=` only
iota-reduces, it does not delta-unfold the `Definition`.  Write
`rewrite /del_es_rel /=` first; only then do `sg_sym` / `sg_irrefl` /`setUC`
find their redexes.  Related: use `sg_sym` (stated on `(--)`, i.e. `edge_rel`),
not the record field `sg_sym'` (stated on `sedge`) — the two differ
syntactically and `rewrite sg_sym'` reports
`The LHS of sg_sym' (sedge _ _) does not match any subterm of the goal`.

### 130. Record projections of `sgraph`/`relType` take the graph implicitly

`sedge (del_edge_set G set0) =2 sedge G` fails
(`expected to have type "Finite.sort (svertex ?s)"`): after `Set Implicit
Arguments`, `sedge`/`edge_rel` take the graph as an *implicit* argument.  State
such equalities as `@edge_rel (del_edge_set G set0) =2 @edge_rel G`, and the
`connected` variants as `@connected (del_edge_set G set0) A` (the named form
`connected (G := …)` does not apply to the *library*'s binder).

### 131. `restrict` is a notation of `preliminaries.v`, not exported by `sgraph`

`connected` unfolds to `connect (restrict S edge_rel)`, but
`From GraphTheory Require Export digraph sgraph` does **not** put `restrict`
(nor `card_bij`) in scope: `digraph.v` only `Require Import`s `preliminaries`
and `bij`.  Add `From GraphTheory Require Import preliminaries bij.` (Import,
not Export, to keep the downstream vocabulary unchanged) when a proof has to
rewrite under `connected`, then `rewrite /restrict_mem` / `eq_connect`.

### 132. `diso` lives in `Type`, so `~ (F ≃ G)` does not typecheck

`Record diso (F G : diGraph) : Type` — writing `~ diso (induced S) H` raises
`has type "Type" while it is expected to have type "Prop" (universe
inconsistency: Cannot enforce Finite.axioms_.u0 <= Prop)`.  Spell the negation
out instead: `forall S : {set G}, diso (induced S) H -> False` (a `forall`
into `False` is a `Prop` whatever the domain's sort).  `#|F| = #|G|` from a
`diso h` is `card_bij (diso_v h)`.

### 133. Re-exporting a library module selectively, to dodge one name clash

`From GraphTheory Require Export minor.` also exports `minor.K4_free` (on
`sgraph`), which shadows the `K4_free` on `iGraph` owned by a downstream
package and breaks a file one does not own.  Coq has no "export all but one",
but abbreviations do the job:

```coq
From GraphTheory Require Import minor.
Notation minor := GraphTheory.core.minor.minor.
Notation strict_minor := GraphTheory.core.minor.strict_minor.
```

The fully-qualified right-hand side avoids self-reference, and the
abbreviations travel through `Require Export base` like any notation.  Before
adding a module to a shared `Require Export`, grep the whole monorepo for
bare re-definitions of its names
(`grep -rnE "^(Definition|Notation|Record|Fixpoint) (matching|connected|K4_free|edge_set|C3|…)\b"`);
the two real clashes found this way were `mgraph.edge_set` (multigraph edges
inside a vertex set, used by chromatic-theory/U5) and `sgraph.C3` (= `'K_3`).

---

*All the sessions logged here drove Rocq through the `rocq-mcp-evolve` MCP
server, developed by the LLM4Rocq project,
<https://github.com/LLM4Rocq/rocq-mcp-evolve> (Apache-2.0; the opam package
still carries its former slug `LLM4Rocq/rocq-tools`) — gratefully
acknowledged.*

---

## Wave X211 (hamiltonicity-theory, Bondy–Murty Hamilton rows, 2026-09-23)

### 134. `Unset Strict Implicit` silently makes the graph argument implicit

`Lemma line_graph_claw_free (G : sgraph) : x211_claw_free (line_graph G).`
unfolds to `forall S, diso (induced S) 'K_1,3 -> False`, so `G` is inferable
from the conclusion and — under the standard
`Set Implicit Arguments. Unset Strict Implicit.` header — becomes IMPLICIT.
`line_graph_claw_free G` then reports

```
The term "G" has type "sgraph" while it is expected to have type
 "induced ?S ≃ 'K_1,3"
```

i.e. `G` was taken for the first EXPLICIT argument (the separator set).  Write
`@line_graph_claw_free G`.  Same trap for every `Definition foo (G : sgraph) :
Prop := forall ...` statement-level notion.

### 135. Views from `bij.v`: `bij_injective'` and the `diso` coercion

`h : induced S ≃ 'K_1,3` coerces to a `bij`, but the coercion is NOT inserted
in view position: `/(bij_injective' h)` fails with *"The term `h` has type
`induced S ≃ 'K_1,3` while it is expected to have type `?f^-1 ?x1 = ?f^-1
?x2`"* (and `/(bij_injective' (diso_v h))` fails too, since `f` is implicit
there as well — see 134).  What works:
`move/eqP/val_inj/(@bij_injective' _ _ (diso_v h))`.
Companion facts: `edge_diso' h x y : h^-1 x -- h^-1 y = x -- y` transports
adjacency from the model to the induced subgraph, and `induced_edge` rewrites
`x -- y` in `induced S` to `val x -- val y`.  To discriminate `inr i = inr j`
in `'K_n,m` (vertices are `'I_n + 'I_m`), `case`/`[]` leaves an equation the
`f_equal val` view cannot digest; use an explicit projection:
`move: (f_equal (fun z : 'K_1,3 => if z is inr k then k else ord0) e)`.

### 136. Never `rewrite card_ord` in a hypothesis that mentions a tuple of length `#|G|`

With `c : (#|G|).-tuple G`, `rewrite card_ord` in `hc : ... size c == #|'K_1|`
fails with a *Dependent type error in rewrite* — `#|'K_1|` also occurs in the
implicit length argument of `tval c`.  Work on the SEQ instead:

```coq
have sz := size_tuple c.                     (* size (tval c) = #|G| *)
case E : (tval c) => [|x [|y s]]; rewrite E in sz uc.
- by move: sz; rewrite card_ord.             (* now #|'K_1| is a plain nat *)
```

`case E : (tval c)` (not `case: (tval c)`) is what lets the two hypotheses be
rewritten afterwards.  Dually, to BUILD such a tuple:
`have sz : size s == #|'K_4| by rewrite /= card_ord.` then
`exists (@Tuple #|'K_4| 'K_4 s sz)`.

### 137. `move: h; rewrite …` rewrites the CONCLUSION too

`move: vc; rewrite /lg_ends !inE => /orP[] /eqP <-; rewrite vi` looks like it
only massages `vc`, but after `move:` the hypothesis is part of the goal, so
`/lg_ends !inE` also unfolds the conclusion — and the later `rewrite vi` then
reports *"The LHS of vi does not match any subterm of the goal"*.  Keep such a
rewrite local:

```coq
have vab : (v == a) || (v == b) by move: vc; rewrite /lg_ends !inE.
by case/orP: vab => /eqP <-; rewrite vi ?orbT.
```

(Note the `<-` direction: the goal mentions the `pose`d names `a`/`b`, so the
equation `v = a` must be used right-to-left.)

### 138. Small set-cardinality identities that do NOT exist under the expected name

`setD1E` (`A :\ x = A :\: [set x]`) is not in this MathComp; for
`#|[set: T] :\ x|` use

```coq
Lemma card_setT_D1 (T : finType) (x : T) : #|[set: T] :\ x| = #|T| - 1.
Proof. by rewrite -cardsT [in RHS](cardsD1 x) in_setT add1n subn1. Qed.
```

(the `[in RHS]` is needed: `cardsD1` would otherwise fire on the left).
Also: after `rewrite cards_eq0` the goal is `A == set0`, so `apply/setP` fails
— it is `apply/eqP/setP`.  And `#|components A| <= 1` for a connected `A`
comes from `card_gt1P` + `components_nonempty` + `components_subset` +
`pblock_equivalence_partition (@sedge_equiv_in G A)` + `def_pblock` +
`trivIsetP`, not from any single library lemma.

### 139. Exhaustive `vm_compute` over `{set {set G}}` is not a grounding strategy

Counting Hamilton cycles of `'K_4` as edge sets
(`#|[set A : {set {set 'K_4}} | [exists c : 4.-tuple 'K_4, …]]| = 3`) sweeps
2^16 collections × 256 tuples: `vm_compute` did not finish in 6 CPU-minutes
(and even ONE comparison `x211_cycle_edges 'K_4 s1 != x211_cycle_edges 'K_4 s2`
times out).  Ground such a counter with cheap one-sided facts instead — an
explicit witness for `0 < #|…|` (via `apply/card_gt0P; exists …; rewrite inE;
apply/existsP; exists (@Tuple …)`) and a degenerate graph for `#|…| = 0` — and
say in the file why the exact count is not machine-checked.

### 140. Guards found by brute force before writing the statement

Two of the seven rows needed a `2 < #|G|` guard that the source leaves
implicit, and a 30-line Python enumeration over all graphs on ≤ 7 vertices is
what pinned them down: the edgeless graph on two vertices IS bipartite and
hypotraceable under the `seq`-based `traceable` of `GTBase.common` (no Hamilton
path; each one-vertex deletion has one), and `'K_1` is vacuously k-tough for
every k while not being Hamiltonian.  Both degenerate witnesses then became
`guard-has-teeth` lemmas in `grounding_X211.v`, so the guard is documented by a
proof rather than by a comment.

## Waves X227 / X228 / X216 (homomorphism-, topological-, infinite-graph-theory, 2026-09-23)

### 141. `permP` and `perm1` are shadowed by `path.v`'s seq-permutation lemmas

`From mathcomp Require Import fingroup perm` does NOT give you the `{perm T}`
lemmas under their short names: `all_boot` (through `path.v`) already owns
`permP : reflect (count^~ _ =1 count^~ _) (perm_eq _ _)` and `perm1`, so
`apply/permP` on a goal `p = 1%g` fails with *Cannot apply view permP* and
`rewrite perm1` with *The LHS of perm1 … does not match*.  Use the qualified
names `perm.permP` (an `iff`, so `apply/perm.permP => d` on `p = q`) and
`perm.perm1`.  Symptom to recognise: the group unit prints as `1%R`, not `1%g`,
because the ring scope is the one open.

### 142. `disjoint0` is about `pred0`, not about `set0`

`[disjoint set0 & A]` is NOT closed by `rewrite disjoint0` (that lemma of
`fintype.v` has LHS `[disjoint pred0 & _]`), and there is no `disjoints0` in
mathcomp 2.5.  Use `rewrite disjoints_subset sub0set`, and for the mirror image
`[disjoint A & set0]` prefix it with `disjoint_sym`.

### 143. `#|{set T}| = 2 ^ #|T|` has no direct name

There is no `card_set`.  Go through the powerset:
`have <- : #|powerset [set: T]| = #|{set T}| by rewrite powersetT cardsT.`
then `rewrite card_powerset cardsT`.

### 144. `cards1P` and friends want the BOOLEAN hypothesis

`cards1P : #|A| == 1 -> exists x, A = [set x]` takes `_ == _`, so a
`c1 : #|A| = 1` obtained by `cardsD1`-style arithmetic must be converted:
`have /cards1P[a Ha] : #|A| == 1 by rewrite c1.`  Same trap for `card_gt1P`
(which, unlike this one, is a `reflect` and destructs as
`[x [y [xA yA xy]]]`).

### 145. `case: #|G| h` parses as an application

`case: #|G| cn0 => // m _` fails with *The variable cn0 was not found*: the
notation `#|_|` swallows the next token, so `#|G| cn0` is read as one term.
Write `case: (#|G|) cn0` or, more robustly, `move: cn0; case: (#|G|)`.

### 146. A record with `Prop` fields is not a `finType`: enumerate it as a `{set …}`

`GTBase.surface`'s `surface_embedding` packs a `{perm surface_dart G}` with two
`Prop`-valued equations, so it cannot be summed over — fatal for a row that
averages a quantity over ALL rotation systems.  The fix that keeps the wave on
base's vocabulary: define the same notion as a boolean subset of the finite
group, `[set p | [forall d, …] && [forall d, porbit p d == …]]`, transcribing
the record's fields one by one, and then prove the BRIDGE back in the grounding
file by applying the record constructor to `eqP`-views of the two `forall`s:
`exists (@SurfaceEmbedding G p (fun d => eqP (H1 d)) (fun d => eqP (H2 d)))`.
The face count is then definitionally the record's, so the bridge lemma closes
with `by exists …`.

### 147. mathcomp-classical cannot be used under the "`Print Assumptions` clean" rule

`cardinality.v`'s `countable`, `#<=`, `finite_set` and `classical_sets`' `set T`
all go through `boolp.asbool`, which is defined from the three classical axioms
(`functional_extensionality_dep`, `propositional_extensionality`,
`constructive_indefinite_description`).  Any lemma mentioning them reports those
axioms, so an infinite-graph row that must stay axiom-free keeps
`igraph.v`'s hand-rolled `infinite_graph` / `card_le` instead — record the
reason in the file header rather than re-litigating it per wave.

### 148. Boolean trichotomy on `nat`: `rewrite neq_ltn; case: ltngtP`

`(x != y) = (x < y) (+) (y < x)` is not `by []`, and naming the branches of
`case: (ltngtP x y) => [lt|gt|->]` to rewrite with them fails, because the
`compare_nat` variant has ALREADY substituted every `x < y` / `x == y` in the
goal.  `by rewrite neq_ltn; case: ltngtP.` closes all three branches by
computation.  The same trick specialises to `'I_n` after `rewrite -val_eqE`.

## Waves X216 / X217 / X227 (graph-theory-misc: complexity, cops-and-robbers, hat guessing, 2026-09-23)

### 149. A lemma proved inside a `Section` over `Variable G : sgraph` needs `@`, not `(v := …)`

`cops.v` proves `cops_win_dominating (v : G) : (forall u, u != v -> v -- u) -> cops_win 1`
inside a section.  After `End`, `G` is INFERABLE from `v`, so `Set Implicit
Arguments` makes it implicit — and then `apply: (cops_win_dominating (v := ord0))`
fails with *Cannot apply lemma*: the named argument is elaborated before the goal
fixes `G`, so `ord0 : 'I_?` has no type.  Write the graph first:
`apply: (@cops_win_dominating 'K_n.+1 ord0)`.  Same trap for every
`Lemma foo (n : nat) : P 'K_n.+1` — `n` is implicit, so `foo 3` silently passes `3`
as the NEXT explicit argument (here a vertex), giving *The term "3" has type "nat"
while it is expected to have type "is_true (?x \in [set: 'K_?n])"*.

### 150. Adjacency goals in `'K_n` / `'K_n,m`: `rewrite /edge_rel /=`, then stop

`x -- y` in `'K_n` is `x != y` and in `'K_n,m` is `is_inl x (+) is_inl y`, but only
after `rewrite /edge_rel /=`.  Two follow-up traps: (a) the reduction often closes
the goal completely, so an extra `eqxx` / `!inE` in the same `rewrite` chain fails
with *The LHS of eqxx does not match any subterm* — reduce first, look, then add;
(b) `(ord1 u)` (`u : 'I_1`, i.e. `u = ord0`) is the standard way to kill the
`'K_1` cases, and it must come BEFORE `/edge_rel`, because the goal only becomes
`false -> …` once both sides are `ord0`.  A `pose v0 : 'K_1 := ord0` must be
unfolded by hand (`rewrite /v0`): `simpl` does not unfold a `pose`.

### 151. `rewrite -(deg_Kn x)` when the rewritten `0` also indexes the graph type

Turning the goal `#|N(x) :&: S| <= 0` into `… <= #|N(x)|` with
`rewrite -(@deg_Kn 0 x)` (where `deg_Kn (n : nat) (x : 'K_n.+1) : #|N(x)| = n`)
fails with a *Dependent type error*: the abstraction over the `0` also captures the
`0` inside `'K_0.+1`, so `x` no longer typechecks.  Rewrite in a HYPOTHESIS instead:
```coq
have H0 : #|N(x)| = 0 := @deg_Kn 0 x.
have Hsub : #|N(x) :&: S| <= #|N(x)| by apply: subset_leq_card; exact: subsetIl.
by rewrite H0 in Hsub.
```

### 152. `{in S &, forall u v, P}` takes NO type annotations

`have Hst : {in S &, forall u v : 'K_n.+1, ~~ u -- v}.` is a *Syntax error: ','
expected after [open_binders]*.  Drop the annotation (`{in S &, forall u v, ~~ u -- v}`);
the types come from `S`.  Build it from the boolean `stable S` with
`apply/stableP; exact: maxstabset_stable HS`, and then apply it as a plain
function: `Hst x y xS yS`.

### 153. Eliminating an `'I_0` inhabitant: `move: (ltn_ord i); rewrite ltn0`

`case: i => m Hm; rewrite ltn0 in Hm` and `apply/existsPn => -[m Hm]; move: Hm;
rewrite ltn0` both raise *Dependent type error in rewrite* (the `m < 0` proof is
used in the ordinal).  The robust idiom keeps the ordinal opaque:
`move: (ltn_ord i); rewrite ltn0.` — the goal becomes `false -> _`.  For a boolean
`[exists i : 'I_0, P i] = false`, combine it with
`apply/negbTE/existsPn => i; by move: (ltn_ord i); rewrite ltn0.`

### 154. `split=> //` on `[/\ A, B, C & D]` leaves SEVERAL goals

Chaining one `by rewrite …` after `split=> //` on a 4-way conjunction silently
applies it to the FIRST surviving goal, which is usually not the one the rewrite
was written for (*The LHS of … does not match any subterm*).  Count the survivors
(`Show` after `split=> //`) and discharge them with `first by …` / bullets.

### 155. `α(A) = 1` on a complete graph: `alphaP`, `card_le1_eqP`, `stabset_bound`

Upper bound: `case: (alphaP [set: 'K_n.+1]) => S HS` replaces `α(…)` by `#|S|` with
`HS : S \in maxstabsets …`; then `apply/card_le1_eqP => x y xS yS` and close with
the stability of `S` (entry 152) plus `rewrite /edge_rel /= negbK eq_sym` — note
`card_le1_eqP` hands you `y == x`, not `x == y`.  Lower bound: `rewrite -(cards1 x);
apply: stabset_bound; rewrite in_stabsets subsetT stable1.`

### 156. A `cite="gc:eNNN"` @EDGE is only checkable after `build_corpus_relations.py`

`build_edge_graph.py --check` resolves the cited corpus relation's endpoints against
`meta/corpus_relations.json`, whose `from_formal_name`/`to_formal_name` are filled
from the MANIFEST.  A wave that authors a new endpoint must regenerate
`meta/v2_corpus_manifest.json` (`build_v2_manifest.py`) AND
`meta/corpus_relations.json` (`build_corpus_relations.py`), in that order, or every
new `gc:` cite fails with *cites corpus relation eNNN, whose endpoints are … -> None*.
With several waves landing concurrently the file is stale until the LAST one
regenerates it; the failure names the offending file, so read the package name in
the error before assuming it is yours.

### 157. `'K_3` inside a binder eats the following comma (`'K_n,m` notation)

`have key : forall i j : 'K_3, P i j` fails with *Syntax error: ',' expected after
[open_binders]*, pointing at a token far to the right.  The culprit is the complete
BIPARTITE notation `''K_' n , m` (`KB`): the parser reads `'K_3, i != j -> …` as
`'K_(3, …)` and then wants another comma.  Parenthesise the type:
`forall i j : ('K_3), …`.  Same for `exists x : ('K_n), …`.  In `(A : {set 'K_3})`
or `#|'K_3|` there is no following comma, so those are fine.

### 158. `have [h|h] := boolP b` (and `eqVneq`) ALREADY rewrites the goal

`boolP` / `eqVneq` return an *indexed* spec, so `case`/`have [..|..] :=` replaces the
scrutinee in the goal: after `have [x2|x2] := boolP (x == v2)` the goal reads
`true != (y == v2)`, not `(x == v2) != (y == v2)`.  A follow-up `rewrite x2` then
fails with *The LHS of x2 (x == v2) does not match any subterm of the goal*, and an
`eqVneq` intro pattern `[->|…]` fails with *The LHS of __top_assumption_ x does not
match any subterm of the goal*.  Just drop the rewrite and read the goal that the
case analysis produced (`; first by []` / `; last by []` usually closes one side).

### 159. `restrict S e x y` is `((x \in S) && (y \in S)) && e x y` — do not `/and3P` it

Stepping through a `connectP` path under `connected S` gives
`restrict S (--) i z && path …`.  `case/andP => /and3P[_ zS iz]` type-checks but
splits the WRONG term: it matches `[&& (i \in S) && (z \in S), i != z & …]`, so the
name bound to "z ∈ S" is really the edge's `i != z`.  The symptom is a later
*Cannot apply lemma (IH z pth zS)*.  Use nested views —
`case/andP => /andP[/andP[_ zS] /andP[_ iz]] pth …` — and confirm with `Show`.

### 160. Proving `is_forest [set: G]` for a concrete G: go through `K3_free_forest`

The `is_forest` definition (uniqueness of irredundant `Path`s) is painful to attack
directly.  `minor.K3_free_forest G : ~ minor G 'K_3 <-> is_forest [set: G]` turns it
into a statement about three branch sets: `case/minorRE => phi [phi0 phiC phiD phiN]`
gives nonempty / connected / pairwise disjoint / pairwise `neighbor`, and
`neighborP` extracts the crossing edge.  The star K_(1,a) needs three lines (at most
one branch set holds the centre, and two leaf-only sets are never adjacent); the path
P_t needs the interval lemma (a connected set of `'I_t` is closed under betweenness,
proved by induction on the `connectP` seq) plus the 8-case ordering.  Disjoint unions
are then free: `join_is_forest (T1 T2 : forest)`, with `@Forest G pf` building the
record.

### 161. `Set Implicit Arguments` silently eats a leading `(n : nat)` binder

`Lemma foo (a : nat) : is_forest [set: star a]` gets `a` IMPLICIT (it is inferable
from the conclusion), so `Forest (foo a)` passes `a` to the FIRST argument of
`is_forest`, i.e. `forall x y, …`, and the error reads *The term "a" has type "nat"
while it is expected to have type "irred ?x /\ …"*.  Write `(@foo a)` whenever a
lemma is used as a term rather than applied by `apply:`.  Conversely this is why
`x226_path_interval cA xA aA lxy lya` works with no explicit set/vertex arguments.

## Waves X217 / X225 (hypergraph-theory: cops and robbers, hypergraph minors, Turán exponents, 2026-09-23)

### 162. A `Fixpoint`'s own recursive call already has its implicit arguments

With `Set Implicit Arguments`, a size argument that later binders determine (here
`c` in `Fixpoint hg_win E (c m : nat) (C : {ffun 'I_c -> T}) r`) is implicit
*inside the body too*: writing `hg_win E c m' C' r'` passes `c` where the fuel is
expected — *The term "m'" has type "nat" while it is expected to have type
"{ffun 'I_?c -> T}"*.  Write the recursive call as `@hg_win E c m' C' r'` (inside a
`Section`, `@` does not ask for the section variables).  Downstream callers then use
the implicit form `hg_win E m C r`; `About` the constant before writing statements.

### 163. `[exists e in E, …]` needs the binder's type, not inference

`Definition hg_link E : rel T := fun u v => [exists e in E, (u \in e) && (v \in e)]`
fails with *The term "e" has type "Finite.sort ?T" while it is expected to have type
"pred_sort ?pT"*: unannotated `E` is elaborated as an abstract predicate type.
Either annotate (`E : {set {set T}}`) or declare `Implicit Types (E : {set {set T}})`
at the top of the section — the latter applies to `Definition` binders as well.
Same cause for a bare `set0` inside such a comprehension: ascribe it,
`[exists e in (set0 : {set {set T}}), …]`.

### 164. `rewrite -(card_ord n)` when `n` occurs in a hypothesis's TYPE

In a goal `#|E| <= 2 ^ n` with `E : {set {set 'I_n}}` in the context, rewriting
`n` backwards into `#|'I_n|` raises *Dependent type error in rewrite … cannot be
applied to … {set 'I__pattern_value_}*: the abstracted `n` also occurs in `E`'s type.
Convert the CONSTANT instead, before introducing the dependent variable:
`have -> : 2 ^ n = #|powerset [set: 'I_n]| by rewrite card_powerset cardsT card_ord.`
then `apply/bigmax_leqP => E _; apply: subset_leq_card; apply/subsetP => A _;
rewrite powersetE subsetT.`

### 165. `[set a; b; c]` is left-nested unions, so `cardsU1` does not apply

`[set a; b]` is `[set a] :|: [set b]`, but `[set a; b; c]` is
`([set a] :|: [set b]) :|: [set c]` — NOT `a |: [set b; c]`, so `rewrite cardsU1`
fails with *The LHS of cardsU1 `#|_ |: _|` does not match*.  Count a 3-element set
with `rewrite cardsU cards2 cards1`, then discharge the intersection with
`have -> : [set a; b] :&: [set c] = set0` (`apply/setP => v; rewrite !inE;
apply/negbTE; apply/negP => /andP[vab /eqP eqv]; rewrite eqv !xpair_eqE /= in vab`)
and `rewrite cards0`.  For pairs of ordinals, `(@Ordinal 3 0 isT == @Ordinal 3 1 isT)
= false` is closed by `by []`, so `xpair_eqE` + `/=` decides distinctness of
explicit pairs.

### 166. Choosing an element of a non-empty `{set T}` constructively

`xchoose` needs the raw reflection view APPLIED to its set: `elimT set0Pn (Bne h)`
fails (*"set0Pn" … while it is expected to have type "reflect ?P ?b"*) because both
of `set0Pn`'s arguments are explicit here.  Use
`pose g h := xchoose (set0Pn (B h) (Bne h))` with
`have gP h : g h \in B h by apply: (xchooseP (set0Pn (B h) (Bne h)))` — the two
proof terms must be written identically.  Injectivity of `g` then gives
`t <= #|T|` by `rewrite -(card_ord t); apply: (leq_card g ginj)`
(`leq_card f injf`, `Arguments leq_card [T T'] f`).  MathComp 2 note:
`[finType of 'I_3]` no longer parses — write `('I_3 : finType)`.

### 167. The rocq MCP session can be shared by concurrent agents

With several subagents running against one rocq-mcp-evolve server, `open`/`step`
state is NOT private: a `step` can come back with another package's goal
(*The variable t was not found in the current environment* while `t` is plainly in
your context, then a goal from a file you never opened), and scratch files written
under a shared scratchpad path can be overwritten mid-run.  Checking one file with
`coqc -R base/theories GTBase -R <pkg>/theories <Ns> -w -notation-overridden <file>`
is race-free and about as fast for a small package; keep `mcp__rocq__build` for the
one-shot "which proofs fail" diagnosis, and give scratch files a wave-specific name.
Also: `mcp__rocq__check` re-runs the script from `Proof.`, so always resubmit the
WHOLE proof, never the remaining half.

### 168. `Syntax error: ',' expected after [open_binders]` when a binder type ENDS with `'K_n`

`forall d : surface_dart 'K_1, P d` and `forall u v : 'K_2, Q u v` both fail to
parse (the error points at the token AFTER the intended comma, i.e. at the end of
the sentence).  The `''K_' n` notation (level 8, `n at level 2`) swallows the rest
of the binder when it is the last token of the type.  Fix: parenthesise the graph,
`forall d : surface_dart ('K_1), …` / `forall u v : ('K_2), …`.  Applications where
`'K_n` is not final (`#|'K_2|`, `x213_edge_colourable 'K_2 1`, `'K_n n.-1`) are fine,
and so is a `Lemma foo (d : surface_dart 'K_1) : …` binder — only the
`forall`/`exists` form with the type ending in `'K_n` breaks.

### 169. `#|'I_d * 'I_t|` does not elaborate — use `#|{: 'I_d * 'I_t}|`

`have cardle : #|'I_d * 'I_t| <= #|K|` fails with *The term "'I_d" has type
"predArgType" while it is expected to have type "nat"*: inside `#| … |` the product
is re-read with `'I_` grabbing the wrong argument.  Write the type-cardinality form
`#|{: 'I_d * 'I_t}|`; `rewrite card_prod !card_ord` then gives `d * t` as expected.
Same file: to embed a `d*t`-element type into a clique `K` use
`@enum_val G (mem K) (widen_ord cardle (enum_rank x))`, whose injectivity follows
from `enum_val_inj`, `val_inj` (widening preserves `val`) and `enum_rank_inj`.

### 170. `case: x` fails with *x is used in hypothesis H* — case-split BEFORE introducing

`move=> unb [c [d H]]; … case: d` is rejected because `d` occurs in `H`.  Either
`case: d H => [|d'] H`, or (better) factor the arithmetic into its own lemma with
no dependent context, e.g. `Lemma expn_leq1 m d : m <= 1 -> m ^ d <= 1`.  The same
trick avoids the dependent-rewrite failure *Illegal application … pred_of_set …*
when a `have a0 : a = 0` would be rewritten inside a term whose TYPE mentions `a`
(`f : G -> {set 'I_a}`): derive the numeric consequence first
(`have ba : b <= a by move: (max_card (mem (f ord0))); rewrite card_ord (card ord0).`)
and only then rewrite in the plain nat inequality.

### 171. `disjointP` / `disjoints0` are not in scope under `GTBase.base`

`[disjoint set0 & set0]` is easiest as `rewrite -setI_eq0 set0I eqxx`;
`[disjoint [set x] & A]` is `disjoints1`.  Nearby names that DO exist and are worth
remembering for grounding files: `set0Pn` (`A != set0` ↔ inhabited), `card_gt0`
(`0 < #|A|` = `A != set0`), `card_gt1P` / `card_gt2P` (two / three distinct elements
of a set), `cardsC1` (`#|[set~ x]| = #|T|.-1`), `card_sig`
(`#|{: {x | P x}}| = #|[pred x | P x]|`, the way to bound `#|induced S|`),
`eq_card0` (`A =i pred0 -> #|A| = 0`, the way to say "this graph has no vertex"),
`card_bij` (needs `From GraphTheory Require Import bij.`) and `minor_card` (GTBase).
`1%g` needs `From mathcomp Require Import fingroup perm.` — without it `%g` is read
in ring scope and `1%g d` fails with *The expression "1%R" … cannot be applied*.

### 172. Naming rule for a `status=verified` `(*@EDGE …*)`: the theorem name is CHECKED

`meta/build_edge_graph.py` splits the `proof=<name>` at the first `_implies_` /
`_equiv_` and requires each half to be a substring of (or to contain) the
corresponding endpoint's name with `_statement` stripped.  So a readable short name
like `gyarfas_sumner_implies_triangle_free_induced_tree` is REJECTED for the edge
`graphs_with_a_forbidden_induced_tree_are_chi_bounded_statement ->
triangle_free_induced_tree_chi_bounded_statement`.  Always name the theorem
`<from without _statement>_implies_<to without _statement>`, however long.
Statuses are `verified` / `candidate` / `refuted-direction` (`verified-literature`
is auto-mapped to `verified`); a `cite="gc:eNNN"` is checked against
`meta/corpus_relations.json`, so that file must be regenerated
(`python3 meta/build_corpus_relations.py`) AFTER `meta/build_v2_manifest.py` when a
wave gives its rows their first formal names.

## Waves X212 / X228 (cycle-theory: Bondy–Murty cycle rows + the 1/2-flow-pair row, 2026-09-23)

### 173. `'K_1,` is parsed as the start of the complete-BIPARTITE notation `'K_ n , m`

`Lemma L (k : nat) : exists S : {set 'K_1}, #|S| <= k /\ (forall c : seq 'K_1, ...)`
fails with

```
Syntax error: ',' expected after [open_binders] (in [binder_constr]).
```

pointing at a token FAR to the right (the `<=` of `k <= size c`), which sends you
hunting for a `forall` / `/\` precedence problem that is not there.  The real cause
is `seq 'K_1,`: coq-graph-theory ships both `'K_ n` (`complete`) and `'K_ n , m`
(`KB`, complete bipartite), so a `'K_<n>` immediately followed by a comma starts
parsing the bipartite notation and swallows the rest of the binder.  Fix: put the
graph in parentheses wherever a comma follows — `forall c : seq ('K_1), …`,
`exists x : ('K_1), …`.  `{set 'K_1}` and `('K_1)` before `)`, `:=` or `->` are
fine; only the comma bites.

### 174. Import `all_algebra` LAST when a required file re-exports `GTBase.base`

WP4b asks a wave file to start with `From GTBase Require Export base.`, and `base.v`
does `From mathcomp Require Export all_boot`.  So `Require Import <your X2nn>` in a
grounding / implications file re-exports `all_boot` — and with it `all_boot`'s
`_ %:R` notation, which overrides the algebra one.  The symptom is an ELABORATION
error in a statement that compiled fine in the wave file:

```
Lemma L (x : int) : 2%:R <= `|x| -> x != 0.
  The term "1" has type "BaseUMagma.sort ?s0" while it is expected to have type
  "Algebra.BaseAddUMagma.sort ?V".
```

A `(2%:R : int)` ascription does NOT help (the notation itself is the wrong one).
Reordering does: put `From mathcomp Require Import all_algebra all_fingroup.` AFTER
every `From Cycle.conjectures Require Import …` line.  This is the same trap as the
`D1.v` header note ("algebra after base"), one level further down the dependency
chain.

### 175. `int` inequality endgames under `Import GRing.Theory Num.Theory`

`lerNgt` and `leNgt` do NOT resolve (the order-theory lemmas live in a module that
is not imported by `Num.Theory`).  Do not chase them; for closing a FALSE numeric
side condition on `int` use instead:

- `(n%:R <= 0)` → `rewrite lern0` (leaves `(n == 0)%N`, then `by []`);
- `((1 : int) <= 0)` → `rewrite ler10`;
- `(m%:R <= n%:R)` → `ler_nat`; `(m%:~R <= n%:~R)` → `ler_int`;
- `x != 0` from `1 <= \`|x|` → `rewrite -normr_gt0; case: \`|x| => // -[]`.

For genuine transitivity (`le_trans`, `ltW`, `le_lt_trans`) the import that works is
the fully qualified `Import mathcomp.order.order.Order.TTheory.` (as in
`grounding_D1.v`); `Import Order.Theory` / `Order.le_trans` do not exist here.

### 176. A `ucycle` hypothesis does not `rewrite` into a `ucycleb` goal

`ucycle e c` is a `Prop` DEFINITION that unfolds to `cycle e c && uniq c`, while
`ucycleb e c` is the boolean of the same body.  A hypothesis `uc : ucycle (--) c`
therefore has statement `cycle (--) c && uniq c`, and `rewrite uc` on a goal
containing `ucycleb (--) c && (2 < size c)` fails with

```
The LHS of uc (cycle (--) c && uniq c) does not match any subterm of the goal
```

even though the two are convertible.  Use conversion instead of rewriting:
`apply/andP; split; [exact: uc | exact: sc]`.  The reverse direction
(`case=> /andP[uc sc]` then `exact: uc` against a `ucycle` goal) works for the same
reason.

### 177. `case: x h => [pat] h` re-introduces `h` BEFORE the pattern variables exist

`move=> e sep; case: e sep => [[e0|]|] sep` then `case: e0` fails with

```
e0 is used in hypothesis sep.
```

because `sep` was re-introduced in every branch, mentioning the freshly created
`e0`.  Either revert again inside the branch (`move: sep; case: e0 => -[]`) or case
the variable together with the hypothesis (`case: e0 sep => -[]`).  Also: a pattern
`[]` for an EMPTY type produces zero subgoals, so it silently shifts every following
`|` of the intro pattern — destructing `edge (two_graph a b)` (which is `void+void`)
inline is what made the first attempt apply `sep` to an edge.

### 178. Triangle inequality on `int` without rewriting under a norm

To get `5%:R <= \`|chi| + \`|b|` from `\`|5%:R * a| = 5%:R` and `chi = 5%:R*a + b`,
rewriting the goal under `\`|_|` needs fragile occurrence selection.  Push the
lemma into a hypothesis and rewrite THERE:

```coq
have h := ler_normD (5%:R * a + b) (- b).
rewrite addrK normrN n5 in h.
```

(`addrK : x + y - y = x` matches because `x - y` is notation for `x + - y`).  Then
cancel with `rewrite -(lerD2r \`|b|); apply: le_trans h.`  Companion facts:
`normrM` + `normr_nat` for `\`|n%:R * a| = n%:R * \`|a||`, and `-natrD` to turn a
numeral into a sum (`(8%:R : int) = 5%:R + 3%:R`).

### 179. `uniq s -> size s <= #|G|`, the workhorse of cycle/path grounding lemmas

`card_uniqP` is a `reflect`, so it cannot be applied directly.  The one-liner that
works is

```coq
Lemma uniq_size (G : sgraph) (s : seq G) : uniq s -> size s <= #|G|.
Proof. by move=> u; rewrite cardT; apply: uniq_leq_size => // x _; rewrite mem_enum. Qed.
```

It gives, for free, "a cycle needs `2 < #|G|`", "a path of length `k` needs
`k < #|G|`", and hence the settled small cases of Kotzig's conjecture and the
non-vacuity of "no cycle inside `'K_1`".

### 180. `bridgeless` in cycle-theory is a DIRECTED-walk notion — pick the witness accordingly

`Cycle.foundations.connectivity.is_bridge e := eseparates (source e) (target e)
[set e]` and coq-graph-theory's `eseparates` quantifies over `walk`, which follows
the intrinsic `source -> target` orientation.  So `~ is_bridge e` means "some
DIRECTED walk joins the ends of `e` without using `e`", i.e. every arc lies on a
directed cycle of the reference orientation.  Consequences for grounding files:
the digon `Gd` of `grounding_U6.v` (two ANTIPARALLEL edges) is NOT bridgeless, and
neither is a directed triangle; the cheapest non-trivial witness is `G2p`
(two PARALLEL edges in the same direction), where each edge's walk is the other:

```coq
Lemma bridgeless_G2p : bridgeless G2p.
Proof.
move=> e; case: e => [x|] sep.
- move: sep; case: x => [e0|] sep.
  + by move: sep; case: e0 => -[].
  + have [f fE fw] := sep [:: None] isT.
    by move: fE fw; rewrite !inE => /eqP ->.
- have [f fE fw] := sep [:: Some None] isT.
  by move: fE fw; rewrite !inE => /eqP ->.
Qed.
```

(`isT` discharges the `walk` premise because `source`/`target` of an `add_edge`
compute.)  Record the directed reading in the row's `Notes:` — it is stronger than
"no cut edge" and is inherited by every statement that reuses `bridgeless`.

### 181. An `external_*_statement` in an `implications_*.v` needs a doc block too

`meta/check_statement_docs.py` targets every `Definition` whose name ends in
`_statement`, implications files included.  The explicit-hypothesis `Prop` that
carries a cited external theorem is not a corpus row, so it must carry
`(** No corpus row: <why> *)` (the convention of `implications_D1.v`), otherwise the
gate reports it as undocumented.

### 182. `Num.Theory` does NOT bring `lexx` / `ltNge` — you also need `all_order`

In a file that opens `ring_scope` for `rat` (arc weights, densities), `Import
GRing.Theory Num.Theory.` gives `ler01`, `ltr01`, `lerD`, `lerDl`, `ltrDl`,
`ltrD2r`, `divff`, `divr_gt0`, `addr_gt0`, `ltr0n`, `ltr_nat`, `pnatr_eq0`
(`mathcomp/algebra/num_theory/numdomain.v`) — but the *order*-level lemmas
`lexx`, `le_gtF`, `lt_geF`, `ltNge`, `ltW` live in `Order.Theory`, which is NOT
re-exported.  `Import Order.Theory.` then fails with *Cannot find module
Order.Theory* unless `order.v` is actually loaded: add
`From mathcomp Require Import all_order.` (the module lives in
`mathcomp/order/{preorder,order}.v`, and `all_algebra` alone does not make the
name resolvable).  Prefer `lerDl`/`ltrDl` over `lexx`+`lerD` when you can; use
`rewrite (lt_geF h)` in a hypothesis `1 <= x` to close a `x < 1` contradiction.

### 183. `simpl` (`/=`, `//=`) on `rat` subterms hangs — reduce only on the `eqType` side

A grounding file computing a weighted-cycle sum blocked `coqc` for minutes on
`rewrite /x_cycle_weight big_cons big_nil addr0 /=`: `simpl` tried to evaluate
`1%:R / 4%:R : rat` (a sigma type with a normalisation proof).  Fix: never let
`/=` see a rational.  Factor the *combinatorial* reduction into standalone
`eqType` lemmas and rewrite with them instead —
`next [:: x] x = x`, `next [:: x; y] x = y`, `x != y -> next [:: x; y] y = x`,
each proved by `rewrite /next /= …` on a plain `eqType`.  Beware the argument
order inside `next_at`: for `next [:: x; y] y` the test that appears is
`y == x`, NOT `x == y`, so `rewrite (negbTE nxy)` fails with *The LHS … does not
match*; derive `have nyx : y != x by rewrite eq_sym` and use that.

### 184. `big_mkcond` is WRONG (and refused) for `\big[minn/m]` — the neutral is not a unit

A "least k with P k, else m" invariant is naturally
`\big[minn/#|D|]_(k < #|D|.+1 | P k) k`, but `minn x m = m` is absorbing, not
neutral, so `big_mkcond` (which needs `Monoid.law idx op`) does not apply and
`rewrite big_mkcond` reports *The LHS of big_mkcond … does not match any
subterm*.  `big_pred1` is unavailable for the same reason.  What works is a
two-line seq induction giving the bound the definition is for:
`Lemma bigmin_le I (r : seq I) P F m : \big[minn/m]_(i <- r | P i) F i <= m`
(`elim: r`, `big_nil`, `big_cons`, `case: (P i) => //`,
`leq_trans (geq_minr _ _) ih`), which then instantiates at the finType index.

### 185. Parameterised one-off digraphs: put the `Type` alias OUTSIDE the section

`core/oriented.v`'s `outsel` pattern is the rule, not an exception:
`Definition my_graph (b : 'Z_4 -> bool) : Type := 'Z_4.` must be declared
*before* the section that declares `Variable b` and the `HB.instance
Definition _ := Finite.on (my_graph b).` / `HasArc.Build (my_graph b) …`; if the
alias is written inside the section its body does not mention `b`, section
discharge drops the parameter and every instance collapses onto one type.  When
the body DOES mention the parameters (`heroes.v`'s `djoin`/`c3sub`,
`(D1 + D2)%type`) the in-section form is fine.  Two unrelated one-off digraphs
may both unfold to `bool`/`'I_n`: the HB instances are keyed on the constant, so
`Definition dg2 : Type := bool.` and `Definition dgl2 : Type := bool.` coexist.
Also: a standalone lemma about such a type needs `#|{: dg2}|`, not `#|dg2|`
(*has type "Type" while it is expected to have type "pred_sort ?pT"*), and
`'Z_n` arithmetic needs `Local Open Scope ring_scope. Import GRing.Theory.`
inside the section (copy `core/tournament.v`'s `C3`).

### 186. Emptiness of `'I_0` / `TT 0`: use `ltn_ord`, not `case: x => m mlt`

`by case: c => [//|[m mlt] s]; move: mlt; rewrite ltn0.` fails with *Dependent
type error in rewrite … Illegal application: Ordinal … cannot be applied*
because `mlt`'s type is what you are rewriting.  Use the projection instead:
`have e0 : forall v : (TT 0 : diGraphType), False by move=> v; have := ltn_ord
v; rewrite ltn0.` and then `case: (e0 v)` everywhere.  The same `e0` builds
functions out of an empty digraph (`fun x => match e0 x with end`), which is how
`unavoidable D 0` and `dgiso D1 D2` are proved for empty digraphs; `bijective`
is a one-constructor Variant, so supply the inverse with
`apply: (@Bijective _ _ _ g)`, not `exists g`.

## Waves X215 / X223 / X229 (extremal-graph-theory: Bondy–Murty extremal & Ramsey, Sidorenko / sparse pairs / VC-dim / induced Turán, robust sublinear expanders, 2026-09-23)

### 187. `rewrite -H` where `H`'s RHS sits next to a graph whose TYPE mentions the same nats

Working in `'K_(2 * k)` with `col : {set 'K_(2 * k)} -> bool`, both

```coq
rewrite -cardE   (* cardE : #|E('K_(2*k))| = k * (2*k).-1 *)
rewrite -split   (* split : #|E(cc col p)| + #|E(cc col q)| = #|E('K_(2*k))| *)
```

fail with *Dependent type error in rewrite of (fun _pattern_value_ : nat => …)*
and a motive mentioning `'K__pattern_value_`: SSReflect abstracts the nat, and
`col`'s type `{set 'K_(2*k)} -> bool` then no longer typechecks.  Two fixes, in
order of preference:

1. **Prove the helper over an ABSTRACT graph.**  `majority_colour (G : sgraph)
   (col : {set G} -> bool) : exists c, #|E(G)| <= 2 * #|E(colour_class col
   (pred1 c))|` rewrites fine inside its own proof (`G` is a variable, nothing
   to abstract) and is then applied at `'K_(2*k)` with no rewriting at all.
2. **Rewrite in the HYPOTHESIS, not the goal**: `rewrite card_edge_Kn bin2 in Hc`
   works where the same rewrite in the goal does not, because the motive is then
   `fun X : nat => X <= …` and the graph never depends on `X`.

Corollary: keep purely arithmetic side-facts (`'C(2*m,2) = m * (2*m).-1`) as
standalone `have`s over a FRESH variable `m`; `case: k k0 …` inside the main
proof fails with *k is used in hypothesis col*.

### 188. `lia` on ssrnat needs `apply/ltP` (or `move/leP`), not just `-!plusE -!multE`

`by rewrite -!plusE -!multE; lia.` fails with *Tactic failure: Cannot find
witness* even on a true goal: `plusE`/`multE` translate `addn`/`muln` but leave
`leq`/`ltn`, which `lia` does not understand.  The working idiom (same as
`packing-theory/theories/foundations/fair_matching.v`) is to move the
comparisons across the reflection first:

```coq
by apply/ltP; rewrite -!plusE -!multE; lia.      (* goal  a < b *)
move/leP: H => H; … ; apply/leP; rewrite -!plusE -!multE in H *; lia.
```

Also clear `.-1` BEFORE calling `lia` (`have -> : (2 * j.+1).-1 = (2 * j).+1 by
rewrite mulnS.`): `predn` is opaque to `lia`.

### 189. `sedge` of a locally built `SGraph`: no `_ -- _ :> G` notation, and `rewrite` of a definitional lemma fails

For `Definition colour_class := SGraph cc_sym cc_irrefl` the goal prints as
`x -- y` but is `@sedge colour_class x y`.  `(x -- y :> colour_class)` is
*Unknown interpretation for notation "_ -- _ :> _"* — write
`@sedge (colour_class col p) x y`.  And a lemma
`colour_class_adj : @sedge colour_class x y = (x -- y) && p (col [set x;y])`
proved `by []` will NOT rewrite (*The LHS of colour_class_adj (sedge _ _) does
not match any subterm of the goal*), because the goal's `sedge` is already
delta-unfolded.  Use `apply/andP; split` / `rewrite /= …` / `by []` instead,
which work up to conversion.  Same story for `del_edge_set`: the goal shows
`x -- y` but the working rewrite chain is
`rewrite /edge_rel /=.` then `rewrite /del_es_rel /= cardF inE andbT.`

### 190. `is_forest [set: 'K_2]` does not compute — use `forestI` + `irred_is_edge`

`apply/is_forestP; vm_compute` times out (`IPath x y` is a finType but its
enumeration does not reduce).  The cheap route is the matroid-free one:

```coq
have key : forall (x y : 'K_2) (p q : Path x y), irred p -> irred q -> p = q.
  move=> x y; case: (eqVneq x y) => [<-|xy] p q ip iq.   (* substitute BEFORE intro'ing p q *)
    by rewrite (irredxx ip) (irredxx iq).
  have E2 : [set x; y] = [set: 'K_2].
    by apply/eqP; rewrite eqEcard subsetT /= cards2 xy cardsT card_ord.
  have [e1 ->] := irred_is_edge p ip xy (fun r z _ => …).
  have [e2 ->] := irred_is_edge q iq xy (…).
  by rewrite (bool_irrelevance e2 e1).
apply: forestI => -[x [y [p1 [p2 [[i1 i2 ne] _]]]]].
by rewrite (key _ _ p1 p2 i1 i2) eqxx in ne.
```

Two traps: (a) `irred_is_edge` takes the PATH explicitly, so it is
`irred_is_edge p ip xy sub`, not `irred_is_edge ip xy sub`; (b) `case: (eqVneq x
y) => [E|xy]` AFTER `p q : Path x y` are in scope leaves you unable to
substitute (`subst y` → *No such hypothesis*, `rewrite -E` → *Dependent type
error*): do the case split on `x`/`y` first, in a `have key : forall x y p q, …`.

### 191. Empty ordinals in a Type-valued goal

`have emb0 : 'K_0 -> 'K_N by case=> m mh; rewrite ltn0 in mh.` fails with *mh is
used in hypothesis _the_hidden_goal_* (the goal is a `Type`, so SSReflect will
not discharge it from a false hypothesis).  In a `Prop` goal
`case: (emb ord0) => m mh; rewrite ltn0 in mh` is fine.  Rather than fight it,
pick a non-degenerate witness: `x215_arrows 1 1` (K_1 arrows K_1 vacuously,
`exists true, id`, then `move: xy; rewrite [x]ord1 [y]ord1 sg_irrefl`) replaces
`x215_arrows N 0` as the non-vacuity lemma and needs no empty function at all.

### 192. Membership goals over `[set uv : G * G | …]` close by `by []`, not by `!eqxx`

`apply/card_gt0P; exists (ord0, Ordinal (isT : 1 < 2)); rewrite !inE.` leaves
`((ord0, _).1 == ord0) && … && (ord0, _).1 -- (ord0, _).2`.  `rewrite !eqxx`
fails (*The LHS of eqxx (_ == _) does not match any subterm*) because the pair
projections are not reduced; plain `by []` evaluates the whole boolean and
closes it.  Likewise `[set uv | …] = set0` for a graph with no edges needs
`rewrite !inE [uv.1 -- uv.2](_ : _ = false) ?andbF` (a `rewrite /= andbF` does
not fire when `sedge` is a `DiGraph`/`SGraph` constant).

### 193. `#|A| <= #|T|` and `\max` attainment

`rewrite -cK2` (with `cK2 : #|'K_2| = 2`) in a goal mentioning `U : {set 'K_2}`
hits the same dependent-rewrite wall as 182; use
`have HU : #|U| <= 2 by have := max_card (mem U); rewrite card_ord.`
For `Delta G = \max_(x : G) #|N(x)|`, the way to push a per-vertex bound through
is `eq_bigmax`:

```coq
have [x0 Hx0] := eq_bigmax (fun x : G => #|N(x)|) G0.   (* G0 : 0 < #|G| *)
rewrite /Delta Hx0; exact: H.
```

and `#|N(v)| < #|N[v]|` is `proper_card (opn_proper_cln v)` (NOT
`rewrite -proper_card`, whose RHS is `true`).

### 194. `exists x : 'K_2, P x` is a syntax error

Same root cause as 168 (`'K_ n , m`): inside an `exists`/`forall` binder a
`'K_<n>` followed by a comma starts the complete-bipartite notation.  Here the
fix is to avoid the binder altogether — `have /card_gt0P[x xU] : 0 < #|U| by …`
gives the witness directly and is shorter than `exists (x : ('K_2)), …`.

## Waves X214 / X220 / X228 (minor-theory: Bondy–Murty minors, width parameters, queue number, 2026-09-23)

### 195. `leq_card` takes the function EXPLICITLY — `exact: leq_card inj` often fails

`leq_card : forall [T T'] (f : T -> T'), injective f -> #|T| <= #|T'|` — `f` is
an *explicit* argument, so `exact: leq_card (isubgraph_inj i)` reports
*Cannot apply lemma* (it tries `isubgraph_inj i` as the function).  Spell the
function out: `exact: (@leq_card _ _ (isubgraph_fun i) (isubgraph_inj i))`.
Same for a record projection: `(@leq_card _ _ (sdm_branch m) (@sdm_inj _ _ m))`.

### 196. `Unset Strict Implicit` makes a record's Prop projections over-implicit

In a file with the usual `Set Implicit Arguments. Unset Strict Implicit.` header,
the projection of a `Record R (A B : sgraph) := Mk { f : ...; f_inj : injective f; ... }`
gets its *record* argument made implicit too (it is inferable from the later
`injective` equation), so `sdm_inj m` elaborates `m` as the equation and fails with
*"m has type subdiv_model H G while it is expected to have type sdm_branch ?s ?x1 = …"*.
Write `@sdm_inj _ _ m`.  Data projections (`sdm_branch m`) are unaffected.

### 197. `'K_n` swallows a following comma: `'K_2,` parses as `'K_n,m`

`[/\ ~ has_induced_copy 'K_0 'K_2, ~ P, … ]` fails with *"has type Prop while it
is expected to have type nat"*: the notation `'K_ n , m` (= `KB n m`) grabs the
`,` of the `[/\ … ]` list and the next conjunct as `m`.  Parenthesise the
complete graph — `('K_2),` — whenever a `'K_n` is immediately followed by a comma
(this bit both `[/\ A, B & C]` lists and `exists x : 'K_2, …`).

### 198. `#|T| = 0` ⟹ absurd: factor it through one lemma, never `rewrite … in hx`

`have hx : 0 < #|H| by apply/card_gt0P; exists x.` followed by
`rewrite H0 in hx` inside the *same* `by` fails (*No such hypothesis*), and
rewriting an ordinal's proof component breaks dependency.  Write the helper once:
`Lemma card0_absurd (T : finType) (x : T) : #|T| = 0 -> False.`
`Proof. move=> T0; have hx : 0 < #|T| by apply/card_gt0P; exists x. by rewrite T0 in hx. Qed.`
then `case: (card0_absurd x G0)` (note `case:`, not `exact:` — the goal is not `False`).
For `'K_0 = complete 0` the sibling `K0_void (x : 'K_0) : False` is proved by
`by case: x => m; rewrite ltn0` — that works only because the goal `False` does
not mention `x` (cf. entry 181).

### 199. Proving `#|G| = 0` : `apply/eqP; rewrite -leqn0 leqNgt; apply/negP => /card_gt0P[x _]`

`cards_eq0` is about `{set T}`, not about `#|T|`, so it does not apply to a
type-level cardinality; `rewrite -leqn0; apply/negP` fails because `_ <= 0` is
not syntactically a negation.  The working chain adds `leqNgt`.

### 200. `n`! and dependent rewriting: never `rewrite n0` when a hypothesis' type mentions `n`

With `F : {set {ffun 'I_n * 'I_n -> bool}}` in the context, `rewrite n0` (where
`n0 : n = 0`) dies with *Dependent type error … pred_of_set cannot be applied*.
Rewrite only in places where `n` is a plain `nat`: `rewrite exp1n muln1;`
`have -> : n`! = 1 by rewrite n0 fact0.`, then `apply: (leq_trans (max_card _))`
and only afterwards `rewrite card_ffun card_prod !card_ord n0 expn0`.

### 201. Arithmetic shapes that must match the lemma, not the informal formula

* `divnMDl q m : 0 < d -> (q * d + m) %/ d = q + m %/ d` — the multiple must be
  written `c * 2 + 1`, NOT `2 * c + 1`, or the rewrite does not fire.
* `leq_divLR` needs `d %| m`; for a ceiling bound use
  `leq_div2r 2 (_ : n.+1 <= c * 2 + 1)` followed by `divnMDl // divn_small //`.
* `leq_trans` cannot bridge two strict inequalities: `leq_trans ac cd` with
  `ac : a < c`, `cd : c < d` fails; use `leq_ltn_trans` and start from
  `leq_ltn_trans (leq0n _) ac : 0 < c`.
* `ceil_div n 2` unfolds to `(n + 2 - 1) %/ 2`; normalise with
  `have -> : n + 2 - 1 = n.+1 by rewrite addn2 subn1.`

### 202. `[set x; y; z]` has no `cardsU1` shape — avoid 3-element cardinalities

`rewrite cardsU1` / `set_cons` / `!inE` all fail on `#|[set x; y; z]|`.  To show
a graph with `#|G| <= 2` is triangle-free, do not count a 3-set: use
`cards2` on `[set x; y]`, `eqEcard` + `subsetT` to get `[set x; y] = [set: G]`,
then `z \in [set x; y]` and `rewrite e sg_irrefl in zx`.

### 203. Inhabiting a `Record` behind `inhabited`: `split; exists …` does not work

`split` on `inhabited R` leaves the goal `R`; `exists f g` then reports
*No such goal* (a record with proof fields is not an iterated `ex`).  Build the
model once as a `Definition … : R. Proof. apply: (@Mk … data …). … Defined.`
(`Defined`, so the projections still reduce in later `rewrite … /=`), and reuse
it: `by split; exact: triv_subdiv_model`.

### 204. Small verified habits of this wave

* `#|induced S| = #|S|` is `by rewrite card_sig; apply: eq_card => x; rewrite !inE.`
* `diso G H -> #|G| = #|H|` goes through `iso_subgraph` + `diso_sym` and
  `leq_card` in both directions (there is no `card_diso`).
* `Kn_clique` has `n` implicit *and* takes the clique's own arguments, so a
  `rewrite (chi_clique (Kn_clique n))` must be `(@Kn_clique n)`.
* `uniq s -> size s <= #|T|` is `by move/card_uniqP => <-; exact: max_card.`
* A four-field `[/\ A, B, C & D]` whose third component ends in
  `exists v : G, f v = i` does *not* re-parse as `exists2`; `Print` the
  definition once to be sure, then keep it.

### 205. `case: ifPn` erases the condition — you cannot `/eqP ->` it afterwards

When the `if`-condition occurs **only inside the `if`**, `case: ifPn => [/eqP ->|ne]`
fails with *The LHS of __top_assumption_ does not match any subterm of the goal*:
`case:` has already replaced every occurrence of the condition by `true`/`false`,
so the introduced equation has nothing left to rewrite.  Two fixes:

* if you only need the branch, intro it as `_`: `case: ifPn => _`;
* if you need the equation to evaluate a **second**, nested `if` (e.g.
  `#|edges x y| + #|edges y x|`, where the second `if` tests
  `x212_rot y == x`), do the case split on the boolean *before* destructing the
  `if`s: `case E: (x212_rot x == y)`, then `move/eqP: E => <-` to substitute.
  Better still, first collapse each `if` to a `nat_of_bool`
  (`#|edges x y| = nat_of_bool (x212_rot x == y)`) and let `by case: (…)` finish.

Corollary for `eqVneq`: `case: (eqVneq e x) => [->|nex]` *also* rewrites `e == x`
to `true`/`false` in the goal, so a follow-up `rewrite (negbTE nex)` fails.  Use
`case E: (e == x)` when you want the literal boolean to survive as a named
hypothesis you can rewrite with later.

### 206. `rewrite /=` destroys concrete-graph `source`/`target` — use walk constructors

On a concrete multigraph built by nested `mgraph.add_edge`, `rewrite /=` inside a
`uwalk (source e) (target e) [:: e']` goal unfolds `endpoint` past the point where
the abstraction lemmas (`src_Gt e : source e = inl tt`) still match, giving
*The LHS of (src_Gt e) (source e) does not match any subterm of the goal*.
Never `/=` such a goal.  Build the walk from generic, `source`/`target`-opaque
constructors instead (added to `Cycle.foundations.connectivity`):

```coq
Lemma uwalk_cons     : source f = x -> uwalk (target f) y w -> uwalk x y (f :: w).
Lemma uwalk_cons_rev : target f = x -> uwalk (source f) y w -> uwalk x y (f :: w).
Lemma uwalk_one      : source f = x -> target f = y -> uwalk x y [:: f].
Lemma uwalk_one_rev  : target f = x -> source f = y -> uwalk x y [:: f].
```

each proved by `by move=> <- <-; rewrite /= !eqxx.` (`… orbT` for the reversed
ones) *while `f` is still abstract*, which is the only place `/=` is safe.  Then
`apply: uwalk_one; rewrite ?src_Gt ?tgt_Gt` works on any carrier.  The `?` (zero
or more) matters: on some carriers the abstraction lemma is a `Proof. by []. Qed.`
identity and the rewrite would fail with `!`.

### 207. Undirected vs directed vocabulary in coq-graph-theory `mgraph`

An `mgraph` used to encode an **undirected** multigraph (one arc per edge) needs
every predicate to be invariant under reversing an arc.  Checklist, learned while
repairing `cycle-theory`:

* SAFE (already symmetric): `incident x e`, `edges_at x`, hence `mdeg`/`subdeg`
  and everything built on them; `[set e | (source e \in S) (+) (target e \in S)]`.
* UNSAFE: `mgraph.walk` (traverses `source → target` only) and therefore
  `mgraph.eseparates`; use `GTBase.base.uwalk` (`base.v:320`) and an
  `ueseparates` stated over it.  A bridge defined with the directed `walk` is
  *far* stronger than "cut edge": it forces out-degree ≥ 2 at the tail and
  in-degree ≥ 2 at the head of every non-loop edge.
* UNSAFE: `mgraph.edges x y = [set e | (source e == x) && (target e == y)]` counts
  arcs in **one** direction; an undirected multiplicity is
  `#|edges x y| + #|edges y x|`.  A bound on `#|edges x y|` alone lets a doubled
  edge through as two antiparallel arcs.

Cheap teeth-lemmas to commit alongside such a repair: the cyclically oriented
triangle is bridgeless *and* simple; a two-vertex one-edge graph has a bridge;
the antiparallel digon is not simple.

### 208. `@Graph unit unit V E ep (fun _ => tt) (fun _ => tt)` for ad-hoc carriers

Nested `mgraph.add_edge` makes case analysis explode (`case=> [[[[[]|[]]|]|]|]`).
For a small cyclic carrier, define it directly: vertices and edges both
`option bool`, `Definition ep (b : bool) (e : V) := if b then rot e else e`, and
`@Graph unit unit V E ep (fun _ => tt) (fun _ => tt)`.  Then
`Lemma src (e : edge Tri) : source e = e. Proof. by []. Qed.` and the analogous
`target e = rot e` are definitional, `#|Tri| = 3` is
`by rewrite /= card_option card_bool`, and every property reduces to
`by case: v => [[]|]`.

## Wave X213 / X219 body repairs (chromatic-theory, second-reader blocks, 2026-09-23)

### 209. `'K_n` in a binder position followed by `,` is parsed as `'K_n , m`

`have deg : forall x : 'K_2, #|N(x)| <= 1.` fails with

```
Syntax error: ',' expected after [open_binders] (in [binder_constr]).
```

because coq-graph-theory declares both `Notation "''K_' n"` (complete graph,
`n at level 2`) and `Notation "''K_' n , m"` (complete bipartite): the parser
grabs the binder's own comma as the separator of the bipartite notation.  The
fix is to spell the head constant out in binder positions —
`forall x : complete 2, ...` — exactly as the curated probe-hint witness for
`arxiv:2004.07457#01` already did.  `[set (ord0 : 'K_2)]` and `'K_2 1` are fine:
only a `'K_n` immediately followed by a comma is at risk.

### 210. Unfolding `edge_rel` through `sjoin` needs two steps, then `sg_irrefl`

For a dart of a disjoint union, `case: d => [[[x|x] [y|y]] p]; move: p;
rewrite /edge_rel /=` leaves `false -> False` on the two mixed constructors but
`x -- y -> False` on the two same-side ones: `/edge_rel /=` peels off
`join_rel` and stops at the inner graph's own `--`.  Do not add a second
`/edge_rel`; finish with the graph's irreflexivity, and make the whole thing one
tactic with `?`:

```coq
by case: d => [[[x|x] [y|y]] p]; move: p;
   rewrite /edge_rel /= ?(ord1 x) ?(ord1 y) ?sg_irrefl.
```

The `?` prefixes are what let the same script close the mixed goals (where `x`
and `y` no longer occur) and the same-side ones.  `sg_irrefl` succeeds where a
literal `eqxx` fails, since after `(ord1 x) (ord1 y)` the goal is `x -- x`, not
`x == x`.

### 211. Disconnectedness from `join_disc`, via `connectedTE`

`~ connected [set: sjoin G H]` is two lines and needs no path reasoning:

```coq
move=> /connectedTE /(_ (inl ord0) (inr ord0)).
by rewrite (@join_disc 'K_1 'K_1).
```

`connectedTE` turns `connected [set: G]` into `forall x y, connect (--) x y`
(dropping the `restrict setT`), and `join_disc` rewrites that instance to
`false`.  The explicit `(@join_disc G1 G2)` is needed: the section variables are
not inferable from the goal's `connect (--) _ _` before the rewrite.

### 212. Existential fold parameters: destructuring and the `0 < b` teeth lemma

Moving a fractional parameter from `forall b, 0 < b -> P b` to
`exists b, 0 < b /\ P b` (X130's `x130_frac_chi_le` shape, the faithful one —
the universal form collapses to `b = 1` whenever the admissible `b` are closed
under addition) changes every consumer:

* introduction becomes `exists 1; split => //; exists F; split` instead of
  `move=> b bpos; exists F; split`;
* elimination is one nested pattern, `move=> [b [bpos [F [Hf Hc]]]]`;
* a downstream lemma that used to fix `b = 1` (`H 1 isT`) must now RETURN the
  witness: `exists (b : nat) (F : 'I_(2 * b) -> {set G}), [/\ 0 < b, ... & ...]`;
* "every vertex is covered" comes from the guard, not from `b = 1`:
  `have : 0 < #|S| by apply: leq_trans (Hc v).` (that is `leq_trans bpos (Hc v)`,
  `1 <= b <= #|S|`), then `rewrite card_gt0 => /set0Pn [i]; rewrite inE`.

Commit the teeth lemma with the repair: at `b = 0` the body holds for EVERY
graph (`exists (fun _ => set0); split => // i; case: i => m; rewrite ltn0`), so
the `0 < b` guard is what carries the content.

### 213. Keep a refuted body's witness alive after the guard is added

When a readback refutes a statement and the repair is a guard, the curated
witness in `meta/probe_hints/` is *supposed* to stop compiling (the vacuity
probe then reports `stale-FIX-OK` instead of `settles` ⇒ FLAGGED).  Re-state the
same refutation in the wave's grounding file against the UNGUARDED condition,
inlined as a `~ (exists C, ...)` with the guard omitted, so the reason for the
guard stays machine-checked and `Print Assumptions`-clean after the row is
repaired.  For `arxiv:2004.07457#01` that is
`grounding_X219.x219_asym_needs_degree_guard` (`trunc_log 2 1 = 0` kills the
list-size lower bound at `DA = DB = 1`).


### 214. `case: ifP` substitutes the condition EVERYWHERE, not just inside the `if`

Proving `(e \in (if c then [set: T] else set0)) = c` with

```coq
rewrite /the_def; case: ifP => h; first by rewrite in_setT h.
```

fails with *"The LHS of h `((i == ord0) || (i == ord_max))` does not match any
subterm of the goal"*.  `ifP` is an `if_spec`, indexed on the boolean, so
`case: ifP` replaces the condition by `true` / `false` in the WHOLE goal — the
right-hand side included.  There is nothing left to rewrite with `h`:

```coq
by rewrite /the_def; case: ifP => _; rewrite ?in_setT ?in_set0.
```

Same trap when the condition also occurs in a hypothesis you meant to reuse:
generalise it first (`move: hyp; case: ifP`) or use `case: (boolP c) => h`,
which does NOT rewrite the goal.

### 215. On a one-element carrier, `rewrite !inE` can close the goal by itself

Witness graphs built over `unit` (`unit_graph tt`, `mgraph.add_edge U tt tt tt`)
have `unit` as their vertex type, and MathComp's `unit` `eqType` has
`eq_op _ _ = true` by computation.  So in

```coq
move=> v; congr (#|_|); apply/setP => e; rewrite !inE.
have tv : x212_tail d e = v.   (* <- "Error: No such goal." *)
```

the `rewrite !inE` already discharged the whole goal: both membership sides
reduced to `(e \in C) && true`.  Symptom: the NEXT tactic fails with *No such
goal*, pointing at a line that looks innocent.  Either finish on that line
(`by move=> v; congr (#|_|); apply/setP => e; rewrite !inE.`) and leave the
human-readable `v = tt` / `source e = tt` lemmas as separate `Lemma`s cited in
a comment, or do the explicit rewriting BEFORE `inE` — but note that inside a
set-builder `[set f in C | P f]` the bound variable is `f`, not `e`, so a
rewrite by `P e = v` has nothing to match until `inE` has exposed it.

### 220. `big_mkcond` rewrites the FIRST big operator, which may be the wrong side

Double counting a `{set}`-valued family (`Σ_v #|{i : v ∈ F i}| = Σ_i #|F i|`)
starts by turning a cardinal into a sum of booleans.  Written inline,

```coq
by rewrite -sum1_card big_mkcond /=; apply: eq_bigr => v _; case: (v \in F i).
```

fails with *"Error: Cannot apply lemma eq_bigr"*: the goal at that point is
`\sum_(v : G) (v \in F i) = #|F i|`, `rewrite -sum1_card` rebuilds the RHS as
`\sum_(v in F i) 1`, and then `big_mkcond` matches the **left** sum first (whose
predicate is `true`), rewriting it to `\sum_v (if true then _ else 0)` and
destroying the alignment the `eq_bigr` was aimed at.

Fix: prove the conversion once, in its own lemma, where there is only one big
operator in sight, and then `rewrite` it wherever needed.

```coq
Lemma card_as_sum (T : finType) (B : {set T}) : #|B| = \sum_(x : T) (x \in B).
Proof. rewrite -sum1_card big_mkcond /=; by apply: eq_bigr => x _; case: (x \in B). Qed.
```

With it, the double count is three lines and no `big_mkcond` ever sees two
candidates:

```coq
transitivity (\sum_(v : G) \sum_(i : 'I_n) (v \in F i)).
  by apply: eq_bigr => v _; rewrite card_as_sum; apply: eq_bigr => i _; rewrite inE.
by rewrite exchange_big /=; apply: eq_bigr => i _; rewrite (card_as_sum (F i)).
```

(The same shape proves "2b induced forests of `K_5` cover at most `4b < 5b`
incidences", i.e. that an existential fold parameter is not vacuous.)

### 221. `sum_nat_const` gives `#|T| * c`, so `cardsT` has nothing to rewrite

`rewrite sum_nat_const cardsT card_ord` on `\sum_(v : 'K_5) b` fails with
*"The LHS of cardsT `#|[set: _]|` does not match any subterm of the goal"*.
`sum_nat_const` on a full-type sum already produces `#|'K_5| * b` — the card of
the **type**, not of `[set: _]` — so `cardsT` is a step too many.  Drop it:

```coq
have -> : 5 * b = \sum_(v : 'K_5) b by rewrite sum_nat_const card_ord.
have -> : 4 * b = \sum_(i : 'I_(2 * b)) 2 by rewrite sum_nat_const card_ord mulnAC.
```

`cardsT` is needed only when the sum was written `\sum_(v in [set: G]) …`.
Note the closing `mulnAC` in the second line: after `card_ord` the goal is
`4 * b = 2 * b * 2`, and `mulnAC` turns the RHS into `2 * 2 * b`, which `done`
closes by conversion.

### 222. `vm_compute` cannot decide anything on a MathComp 2 `finType`

Tempting shortcut for a concrete counterexample graph: build it on `'I_4` /
`'I_6` with an explicit `endpoint` table and discharge `mreg`, `coloring`,
`omega` by computation.  It does not work — MathComp 2 locks the finite
enumeration, so even

```coq
Goal #|'I_4| = 4. Proof. Fail (by vm_compute). Fail (by compute).
Fail (by rewrite unlock; vm_compute). Fail (by rewrite cardT enumT unlock; vm_compute).
by rewrite card_ord. Qed.
```

has all four computational attempts fail (`Error: No applicable tactic.`, i.e.
`vm_compute` leaves `card (T := {| Finite.sort := 'I_4; … |}) …` stuck).  The
same holds for `[forall v : 'I_4, …]`.  So every fact about a concrete finite
graph has to be proved by `setP` + ordinal/`option`/`sum` case analysis, the
style already used in `grounding_U6.v`
(`by case: e => [[[[]|[]]|]|]`), or by the named lemmas (`card_ord`,
`cardsU1`, `cards1`, `sub_chi`, `chi_clique`, `color_bound`).

### 223. `all_algebra` makes bare `+` in a `nat` goal ring addition

In a file that imports `mathcomp.all_algebra` after `base` (the import order of
`D1.v`), a lemma STATEMENT written as

```coq
Lemma mdeg_cut (G : mgraph) (v : G) :
  mdeg v = #|cut [set v]| + (#|loops_at v| + #|loops_at v|).   (* WRONG *)
```

elaborates the right-hand `+` to `GRing.add` on the `nat` semiring, while the
`+` produced by `rewrite subdegE` on the left is `addn`.  The two are
convertible, so the goal *prints* fine —

```
(#|cut [set v]| + #|loops_at v| + #|loops_at v|)%N = #|cut [set v]| + (#|loops_at v| + #|loops_at v|)
```

— but `rewrite addnA` then fails with *"The LHS of addnA `(_ + (_ + _))%N` does
not match any subterm of the goal"*, because `rewrite` matches up to syntax, not
conversion.  The tell is the asymmetric `%N` in the printed goal: one side
carries it, the other does not.  Fix: annotate the statement,

```coq
  mdeg v = (#|cut [set v]| + (#|loops_at v| + #|loops_at v|))%N.
```

(Same trap for `<=`, `*`, and for `have` statements inside such a proof.)

### 224. `exact: addnA` vs `rewrite addnA` — check which way the lemma points

`addnA : m + (n + p) = m + n + p` is stated left-associating.  On a goal
`A + B + B = A + (B + B)` (the shape `cardsUI` leaves after a degree split),
`exact: addnA` fails (*"Cannot apply lemma addnA"*) because the goal is its
symmetry; `by rewrite addnA` works, rewriting the goal's right-hand side.
When a commuted/associated variant is needed, prefer `rewrite` (which can fire
on either side) over `exact`, or spell out `esym (addnA _ _ _)`.  Related:
`mul2n : 2 * n = n.*2` is useless if the `2 * n` in the goal is ring
multiplication — see entry 223 — which is what made the first version of
`mdeg_cut` fail twice in a row for two different reasons.

### 225. Count the brackets: an SSR intro pattern one level too shallow reports `done`'s error

Destructuring an edge of a 6-fold `add_edge` tower (`edge Gcl =
option (option (option (option (option (option ((void+void)+(void+void)))))))`)
needs SIX `[…|]` layers around the base pattern:

```coq
(* WRONG — five layers: 8 leading brackets *)
by case: e => [[[[[[[[]|[]]|[[]|[]]]|]|]|]|]|].
(* RIGHT — six layers: 9 leading brackets *)
by case: e => [[[[[[[[[]|[]]|[[]|[]]]|]|]|]|]|]|].
```

The failure mode is misleading: the *short* pattern does not complain about
arity, it reports the error of ssr's `done` on a fully destructured goal —

```
Error: No assumption in ((Some (Some (Some (Some (Some None)))) == …) = true)
```

with the error located on the `case:` line itself, not on the tactic after it.
Reading that as "the goal is true but `by []` cannot see it" sends you hunting
for a conversion problem that is not there.  Diagnosis: the leading-bracket
count must be (number of `option` layers) + (leading brackets of the base
pattern); here 6 + 3.  Sanity-check the same pattern at depth 1 and 2 first
(`Lemma probe (e : edge Gc1) : e == e.`), where the right shape is obvious.

### 226. Concrete `==` does compute, but only when both sides elaborate alike

Once entry 225 was fixed the real conversion question remained, and the answer
is: `eq_op` on concrete `option`-tower values DOES reduce (`Lemma p : ea != eb.
Proof. by []. Qed.` works), what fails is `rewrite eqxx` / `apply: eq_refl` when
the two sides carry *different but convertible* implicit type arguments.
`Set Printing All` shows it at once:

```
@eq_op (fintype_Finite__to__eqtype_Equality (edge Gcl))
  (@Some (Finite.sort (edge Gc5)) …)                (* from case: e *)
  (@Some (option (option (option (option …)))) …)   (* from Definition ea *)
```

`case:` keeps `Finite.sort (edge Gc5)`, while `Definition ea : edge Gcl := Some
(Some …)` unfolds the sort during elaboration.  `rewrite eqxx` then matches
nothing (`rewrite` is syntactic) and `done`'s hint `eqxx` does not fire either.
Do not fight it with type ascriptions; instead never let the two meet: unfold
the constants FIRST (`rewrite /ea /eb …`) and let the whole boolean reduce by
conversion inside `done`, which is what closes each branch.

### 227. `[set a; b; c]` is left-nested `setU`, so `cardsU1` needs `-setUA`

`[set a; b; c]` elaborates to `[set a] :|: [set b] :|: [set c]`, i.e.
`(setU (setU _ _) _)`, while `cardsU1 : #|x |: A| = (x \notin A) + #|A|` wants
`setU1` at the head.  So

```coq
by rewrite cardsU1 cards2 !inE.        (* "The LHS of cardsU1 #|_ |: _| does not match" *)
by rewrite -setUA cardsU1 cards2 !inE. (* works *)
```

The same left-nesting is why `!inE` turns `e \in [set a; b; c]` into
`(e == a) || (e == b) || (e == c)` *left*-associated, which `or3P` (an
`[|| _, _ | _]` = right-associated view) does NOT match: destructure with
`/orP[/orP[/eqP->|/eqP->]|/eqP->]` instead.  Also: `#|A : {set T}|` does not
parse (the `:` clashes with the `#| |` notation) — name the set with a
`Definition` or write `#|(A : {set T})|`.

### 228. Building a concrete `coloring` without `vm_compute`

MathComp 2's locked `Finite.enum` rules out discharging `coloring P D` by
computation, and proving `partition P D` by hand (cover + `trivIset` + `set0
\notin P`) is painful.  Build it incrementally instead, from
`coloring.empty_coloring` upwards with

```coq
coloringU1 : stable S -> S != set0 -> coloring P H -> [disjoint S & H] ->
             coloring (S |: P) (S :|: H)
```

after rewriting the vertex set into the matching right-nested shape
(`rewrite edgeT_line_Gcl`, where the target is `S1 :|: (S2 :|: (S3 :|: set0))`).
Three bonuses: `#|S1 |: (S2 |: (S3 |: set0))| <= 3` follows from `cardsU1` +
`leq_b1` with NO distinctness proofs; `color_bound` turns it into `χ <= 3`; and
the matching lower bound is `sub_chi` + `chi_clique` on a clique of edges.
Gotchas: state the colour classes at the sgraph type (`Definition S1 : {set
line_graph G} := …`), or `apply: coloringU1` fails to infer the sgraph; and
`[disjoint A & B]` has no `disjointP` in this MathComp — use
`rewrite -setI_eq0; apply/eqP/setP => z; rewrite !inE`.  For non-adjacency in a
line graph, go through `incidentE` (`incident v e = (source e == v) || (target e
== v)`): `[exists b : bool, …]` does not reduce, a disjunction of concrete
equalities does.


### 229. Counting the orbits of a "one cycle per vertex" permutation

`porbits f` is `[set porbit f x | x : T]`, an `imset` over `predT`, so the way
to count it is to re-present it as an image of the SET you actually want and
then use `card_in_imset` (which needs injectivity only `{in A &, …}`):

```coq
pose A := [set v : G | [exists d : surface_dart, (sval d).1 == v]].
pose phi (v : G) := [set d : surface_dart | (sval d).1 == v].
have eqim : porbits (surface_erot E) = [set phi v | v in A].
  apply/setP => X; apply/idP/idP.
    case/imsetP => d _ ->; apply/imsetP; exists (sval d).1.
      by rewrite AE; apply/existsP; exists d.
    by rewrite surface_erot_vertex.
  case/imsetP => v; rewrite AE => /existsP[d /eqP dv] ->.
  by apply/imsetP; exists d; rewrite ?inE // surface_erot_vertex dv.
by rewrite eqim card_in_imset.
```

Two gotchas. `rewrite inE` does NOT unfold a `pose`d set, so membership in `A`
has to go through a `have AE : forall v, (v \in A) = […]` proved by
`rewrite /A inE` (same for `phi`); doing it once keeps the rest of the proof
`rewrite AE`-clean. And in the `⊇` direction the `imsetP` witness carries the
`d \in predT` side goal — `exists d; rewrite ?inE //` discharges it.

### 230. `(2 + E - V - F) %/ 2 = 0` over truncating `nat`

Euler-genus goals are `nat` subtractions, so never chain `leq_sub2l` by hand.
`divn_small` reduces `x %/ 2 = 0` to `x < 2`, and the two subtractions come off
with `leq_subr` + `ltn_subrL`:

```coq
rewrite c0 div0n addn0; apply: divn_small.          (* goal: 2 - #|G| - F < 2 *)
by apply: leq_ltn_trans (leq_subr _ _) _; rewrite ltn_subrL cG.
```

`ltn_subrL : (m - n < m) = (0 < n) && (0 < m)`, so a single `0 < #|G|` closes
it. Corollary worth remembering when auditing such a definition: enlarging `V`
can only DECREASE the computed genus, never increase it, because the excess is
truncated at 0 — that is why the 2026-09-23 vertex-count repair could only make
`surface_embeddable g G` hold for MORE graphs (hypotheses weaker, rows
stronger) and could not break a single downstream proof.

### 231. A dartless graph as an embedding witness

To exhibit a `surface_embedding` on a graph with no dart, take `1%g` and feed
the two record fields by absurdity — `by move=> d; case: (nodart d)` proves both
`surface_erot_src` and `surface_erot_vertex` — and get the edge count from
`eq_card0`. Inside the section the type is `surface_dart`, NOT `surface_dart G`
(the section variable is not yet discharged): writing `surface_dart G` there
fails with "Illegal application (Non-functional construction)", while OUTSIDE
the section it is mandatory. Same for `embedding_of` in
`topological/foundations/embedding.v`, where the canonical rotation already
exists, so the witness is just `exists (embedding_of G)`.

### 232. Editing shared `.v` files without rewriting them

For surgical edits in files other agents also own, replace an exact unique
string with a three-line Python guard (`assert src.count(old) == 1`) rather than
`sed`; `sed -i` on macOS needs a backup suffix and silently edits every match.
Doc blocks checked by `meta/check_statement_docs.py` are safe to extend this
way: the gate checks the KEY ORDER (`Corpus row`/`Site`/`Review`/`English
statement`/`Definitions`/`Notes`) and the URL bytes, and `Notes:` is free text,
so appending a sentence before the closing `*)` — indented so that it cannot be
read as a new key — never breaks the gate.
