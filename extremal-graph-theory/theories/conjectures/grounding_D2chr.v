(** * Extremal.conjectures.grounding_D2chr — grounding lemmas for milestone D2chr.

    SIMPLE, Qed-closed sanity results validating the new primitives introduced in
    [D2chr.v].  For each genuinely new definition we record a satisfiable witness
    and/or at least one textbook identity (uniqueness of the relationally-pinned
    optima, structural identities of the auxiliary predicates, degenerate witnesses
    of the constructive ones).  These are statement-validation lemmas, NOT the (open)
    conjectures themselves — every conjecture row stays statement-only in [D2chr.v].

    Primitives reused verbatim from GTBase.base / GraphTheory.minor / the foundations
    circular layer (Delta, χ, complete, minor, pq_colouring, is_circular_chromatic, …)
    are not re-grounded here; Row 8 introduces no new primitive (it is a direct
    application of [is_circular_chromatic]). *)

From GTBase Require Import base.
From GraphTheory Require Import minor.
From Extremal.foundations Require Import circular_colouring.
From mathcomp Require Import all_algebra.
From Extremal.conjectures Require Import D2chr.
Import GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

(** Antisymmetry of [<=] on [rat], used to turn the two extremal inequalities of an
    "infimum/minimum attained" predicate into a uniqueness statement. *)
Lemma rle_anti (a b : rat) : a <= b -> b <= a -> a = b.
Proof. move=> ab ba; apply: order.Order.POrderTheory.le_anti; rewrite ab ba //. Qed.

(** ** Row 1 — fractional Hadwiger primitives *)

(** [bfold_colouring] is satisfiable: the empty [(0:0)]-fold colouring works. *)
Lemma bfold_colouring_trivial (G : sgraph) :
  @bfold_colouring G 0 0 (fun _ => set0).
Proof. split=> [v|x y _]; first by rewrite cards0. by rewrite -setI_eq0 setI0. Qed.

(** χ_f is uniquely pinned: the attained infimum is a function of [G]. *)
Lemma is_fractional_chromatic_unique (G : sgraph) (r1 r2 : rat) :
  is_fractional_chromatic G r1 -> is_fractional_chromatic G r2 -> r1 = r2.
Proof.
move=> [E1 LB1] [E2 LB2]; apply: rle_anti.
- by case: E2 => a2 [b2 [b2pos [wit2 ->]]]; apply: LB1.
- by case: E1 => a1 [b1 [b1pos [wit1 ->]]]; apply: LB2.
Qed.

(** had(G) is uniquely pinned: the largest clique-minor order is a function of [G]. *)
Lemma is_hadwiger_unique (G : sgraph) (h1 h2 : nat) :
  is_hadwiger G h1 -> is_hadwiger G h2 -> h1 = h2.
Proof.
move=> [m1 U1] [m2 U2]; apply/eqP; rewrite eqn_leq.
by rewrite (U2 _ m1) (U1 _ m2).
Qed.

(** [frac_clique_minor] is satisfiable: the empty branch-set family has total weight 0. *)
Lemma frac_clique_minor_trivial (G : sgraph) :
  @frac_clique_minor G 0 (fun _ => set0) (fun _ => 0) 0.
Proof.
split; try by case.
- by move=> v; rewrite big_ord0.
- by rewrite big_ord0.
Qed.

(** had_f(G) is uniquely pinned: the LP optimum is a function of [G]. *)
Lemma is_fractional_hadwiger_unique (G : sgraph) (r1 r2 : rat) :
  is_fractional_hadwiger G r1 -> is_fractional_hadwiger G r2 -> r1 = r2.
Proof.
move=> [E1 UB1] [E2 UB2]; apply: rle_anti.
- by case: E1 => n1 [B1 [w1 H1]]; apply: (UB2 _ B1 w1).
- by case: E2 => n2 [B2 [w2 H2]]; apply: (UB1 _ B2 w2).
Qed.

(** ** Row 2 — colouring-mixing primitives *)

(** [pqb] is exactly the boolean reflection of the shared Prop-level [pq_colouring]
    (foundations): the two encodings of (p,q)-validity coincide. *)
Lemma pqbP (G : sgraph) p q (c : {ffun G -> 'I_p}) :
  reflect (pq_colouring (fun x y : G => x -- y) p q (fun v => (c v : nat)))
          (@pqb G p q c).
Proof.
apply: (iffP idP).
- move=> /forallP H; split=> [v|u v uv]; first exact: ltn_ord.
  by move/forallP/(_ v): (H u); move/implyP/(_ uv)/andP.
- move=> [_ Hedge]; apply/forallP=> x; apply/forallP=> y; apply/implyP=> xy.
  by apply/andP; apply: Hedge.
Qed.

(** The recolouring relation is irreflexive (a single-vertex move changes a vertex). *)
Lemma recolour_adj_irrefl (G : sgraph) p q (c : {ffun G -> 'I_p}) :
  ~~ @recolour_adj G p q c c.
Proof.
rewrite /recolour_adj.
have -> : [set v | c v != c v] = set0 by apply/setP=> v; rewrite !inE eqxx.
by rewrite cards0 /=; case: (pqb q c).
Qed.

(** The recolouring relation is symmetric. *)
Lemma recolour_adj_sym (G : sgraph) p q (c c' : {ffun G -> 'I_p}) :
  @recolour_adj G p q c c' = @recolour_adj G p q c' c.
Proof.
rewrite /recolour_adj.
have -> : [set v | c v != c' v] = [set v | c' v != c v].
  by apply/setP=> v; rewrite !inE eq_sym.
by rewrite andbCA.
Qed.

(** M_c(G) is uniquely pinned: the (greatest-lower-bound) mixing threshold is a
    function of [G].  This is the textbook identity the infimum reformulation must
    satisfy (it replaces the spurious attained-minimum encoding). *)
Lemma is_colouring_mixing_threshold_unique (G : sgraph) (r1 r2 : rat) :
  is_colouring_mixing_threshold G r1 -> is_colouring_mixing_threshold G r2 -> r1 = r2.
Proof.
move=> [LB1 GT1] [LB2 GT2]; apply: rle_anti.
- exact: (GT2 _ LB1).
- exact: (GT1 _ LB2).
Qed.

(** ** Row 3 — bipartite *)

(** base's [bipartite] (the 2-colouring form) is witnessed e.g. by the 1-vertex
    graph; the standard equivalence with χ≤2 holds but is not needed here. *)
Lemma bipartite_K1 : bipartite 'K_1.
Proof. by exists (fun _ : 'K_1 => false) => x y; rewrite (ord1 x) (ord1 y) sgP. Qed.

(** ** Row 4 — perfect-matching / sign-weight primitives *)

(** [pmatch] is satisfiable: the empty matching on [0] vertices is a (vacuous)
    fixed-point-free involution. *)
Lemma pmatch_n0 (m : {ffun 'I_0 -> 'I_0}) : pmatch m.
Proof. by apply/forallP; case. Qed.

(** [match_weight] of the empty matching is the empty product [1]. *)
Lemma match_weight_n0 (sgn : 'I_0 -> 'I_0 -> int) (m : {ffun 'I_0 -> 'I_0}) :
  @match_weight 0 sgn m = 1 :> int.
Proof. by rewrite /match_weight big_ord0. Qed.

(** [coloring_weight] on the empty vertex set is [1] (one empty matching, weight 1). *)
Lemma coloring_weight_n0 d (sgn : 'I_0 -> 'I_0 -> int) (c : 'I_0 -> 'I_d) :
  @coloring_weight 0 d sgn c = 1 :> int.
Proof.
rewrite /coloring_weight.
under eq_bigr do rewrite match_weight_n0.
rewrite (eq_bigl xpredT); last by move=> m; apply/andP; split; apply/forallP; case.
by rewrite sumr_const card_ffun !card_ord expn0 mulr1n.
Qed.

(** [bicolored_unit] is satisfiable: on [0] vertices, with any [d > 0], the (vacuous)
    sign function gives every constant colouring weight 1 and there is no non-constant
    colouring to cancel. *)
Lemma bicolored_unit_n0 d : (0 < d)%N -> bicolored_unit 0 d.
Proof.
move=> d0; exists (fun _ _ : 'I_0 => 1%Z); split; first by move=> [].
split.
- by move=> k c _; exact: coloring_weight_n0.
- by move=> c Hc; exfalso; apply: Hc; exists (Ordinal d0); case.
Qed.

(** ** Row 5 — little-o(k²) *)

(** [is_o_ksq] is satisfiable: the zero function is o(k²). *)
Lemma is_o_ksq_0 : is_o_ksq (fun _ => 0%N).
Proof. by move=> c _; exists 0%N => k _; rewrite muln0. Qed.

(** ** Row 6 — circular choosability *)

(** Circular [t]-choosability is monotone in [t]: larger lists are easier to colour. *)
Lemma circularly_t_choosable_mono (G : sgraph) (t t' : rat) :
  t <= t' -> circularly_t_choosable G t -> circularly_t_choosable G t'.
Proof.
move=> tt' Ht p q qpos L HL; apply: (Ht p q qpos L) => v.
apply: (order.Order.POrderTheory.le_trans _ (HL v)).
by rewrite ler_pM2r ?tt' // ltr0z.
Qed.

(** Textbook identity for cch(G): strictly above the threshold the graph is choosable. *)
Lemma is_circular_choosability_choosable_above (G : sgraph) (b t : rat) :
  is_circular_choosability G b -> b < t -> circularly_t_choosable G t.
Proof. by case=> _ H _; apply: H. Qed.

(** ** Row 7 — star edge colouring of complete graphs *)

(** ['K_1] has no edges. *)
Lemma complete1_no_edge (x y : complete 1) : (x -- y) = false.
Proof. by rewrite (ord1 x) (ord1 y) sgP. Qed.

(** [star_edge_colouring] / [star_edge_k_colourable] are satisfiable: the constant
    colouring is a star edge colouring of the edgeless ['K_1] with 1 colour. *)
Lemma star_edge_colourable_complete1 : star_edge_k_colourable (complete 1) 1.
Proof.
exists (fun _ _ => ord0); split.
- by split=> [x y|x y z]//; rewrite complete1_no_edge.
- by move=> a b c d e _; rewrite complete1_no_edge.
- by move=> a b c d _; rewrite complete1_no_edge.
Qed.

(** Textbook value: the star chromatic index of ['K_1] is 1 (0 colours cannot colour
    its single vertex's edge function). *)
Lemma is_star_chromatic_index_complete1 : is_star_chromatic_index (complete 1) 1.
Proof.
split; first exact: star_edge_colourable_complete1.
by move=> k' [f _]; exact: leq_ltn_trans (leq0n _) (ltn_ord (f ord0 ord0)).
Qed.

(** ** Row 9 — orthogonality / perpendicularity *)

(** The zero vector is perpendicular to nothing (it is an isolated vertex). *)
Lemma perp0l (R : rcfType) (v : 'rV[R]_3) : @perp R 0 v = false.
Proof. by rewrite /perp eqxx. Qed.

(** Perpendicularity is symmetric (dot product is symmetric). *)
Lemma perp_sym (R : rcfType) (u v : 'rV[R]_3) : @perp R u v = @perp R v u.
Proof.
rewrite /perp.
have dotC : (u *m v^T) 0 0 = (v *m u^T) 0 0.
  by rewrite !mxE; apply: eq_bigr => j _; rewrite !mxE mulrC.
by rewrite dotC andbCA.
Qed.

(** ** Row 5 — little-o(k²) has teeth *)

(** [is_o_ksq] is a GENUINE constraint: [k²] itself is NOT o(k²) (complements
    [is_o_ksq_0], which only shows the zero function qualifies — so the predicate
    is not vacuously satisfied by every [f]).  Instantiating the [c = 2] regime, a
    large [k] would force [2·k² ≤ k²], impossible once [k² > 0]. *)
Lemma not_is_o_ksq_sq : ~ is_o_ksq (fun k => k * k)%N.
Proof.
move=> /(_ 2 isT) [N H].
set k := maxn N 1.
have kN : (N <= k)%N by exact: leq_maxl.
have k0 : (0 < k)%N by rewrite /k leq_max orbT.
have kk0 : (0 < k * k)%N by rewrite muln_gt0 k0.
have hk : (2 * (k * k) <= k * k)%N by exact: (H k kN).
by move: hk; rewrite -{2}(mul1n (k * k))%N (leq_pmul2r kk0).
Qed.

(** ** Technique #3 — independent re-encodings with a proved equivalence

    For two load-bearing definitions we record a SECOND, structurally different
    encoding and prove it equivalent (Qed, axiom-free).  Agreement between two
    independent formalizations is the faithfulness evidence: neither <-> is a
    definitional restatement — each needs a genuine induction / algebraic bridge. *)

(** *** [graph_power] (base) — neighbourhood-closure vs bounded walk.

    base defines reachability inside the [m]-th power via the iterated
    neighbourhood-SET closure [ball]: [reach_le m x y := y \in ball m x], where
    [ball 0 x = [set x]] and [ball k.+1 x = ball k x :|: \bigcup_{z in ball k x} N(z)]
    — a global, quantifier-free set fixpoint.  The independent characterization is
    the textbook one: [y] is reachable from [x] in at most [m] steps iff there is a
    WALK (an explicit [path]/[last] witness, mathcomp's shape) of length [<= m] from
    [x] to [y].  The equivalence is proved by induction on [m], peeling the last
    edge with [rcons_path]/[last_rcons] and using [bigcupP]/[in_opn] — it is NOT
    reflexivity. *)
Definition reach_le_alt (G : sgraph) (m : nat) (x y : G) : Prop :=
  exists p : seq G, [/\ path (--) x p, last x p = y & (size p <= m)%N].

Lemma reach_le_altE (G : sgraph) (m : nat) (x y : G) :
  reach_le m x y <-> reach_le_alt m x y.
Proof.
rewrite /reach_le /reach_le_alt.
elim: m y => [|m IH] y /=.
- rewrite inE; split.
  + move/eqP => xy; exists [::]; split => //=; by rewrite xy.
  + move=> [p [pp lp sp]]; move: sp; rewrite leqn0 => /nilP p0.
    by rewrite -lp p0 /= eqxx.
- rewrite inE; split.
  + case/orP => [yb | /bigcupP[z zb zy]].
    * have [p [pp lp sp]] := (proj1 (IH y)) yb.
      by exists p; split => //; exact: (leqW sp).
    * have [q [pq lq sq]] := (proj1 (IH z)) zb.
      rewrite in_opn in zy.
      exists (rcons q y); rewrite rcons_path last_rcons size_rcons lq.
      split; [ by rewrite pq zy | by [] | by rewrite ltnS ].
  + move=> [p [pp lp sp]].
    move: sp; rewrite leq_eqVlt ltnS => /orP[/eqP sz | sle].
    * apply/orP; right; apply/bigcupP.
      move: sz pp lp; case: (lastP p) => [|q w].
      -- by [].
      -- rewrite size_rcons rcons_path last_rcons => -[sq] /andP[pq edge] lw.
         exists (last x q); last by rewrite in_opn -lw.
         apply: (proj2 (IH (last x q))); exists q; split => //.
         by rewrite sq.
    * apply/orP; left; apply: (proj2 (IH y)); exists p; split => //.
Qed.

(** The [graph_power] adjacency itself, unfolded through the walk encoding. *)
Lemma pow_relE (G : sgraph) (m : nat) (x y : G) :
  pow_rel m x y <-> (x != y) /\ (reach_le_alt m x y \/ reach_le_alt m y x).
Proof.
rewrite /pow_rel; split.
- move=> /andP[nxy /orP[r|r]]; (split; first exact: nxy);
    [left|right]; exact/reach_le_altE.
- move=> [nxy H]; rewrite nxy /=; apply/orP.
  by case: H => /reach_le_altE r; [left|right].
Qed.

(** *** [pq_colouring] (foundations) — linear band vs cyclic metric.

    [circular_colouring.pq_colouring] follows the source verbatim: on every edge
    [uv], the LINEAR colour distance [d := |c u - c v|] lies in the two-sided band
    [q <= d <= p - q].  The standard Vince/Zhu textbook definition instead uses the
    CYCLIC metric on the palette [Z/p] and a single min-based lower bound:
    [q <= circ_dist p (c u) (c v)] with [circ_dist p a b := minn |a-b| (p - |a-b|)].
    Proving these equivalent is exactly the faithfulness check an off-by-one in the
    band ([p-q] vs [p-q-1], or [<] vs [<=]) would break: it needs [d < p] (from the
    colour bound, [absz_sub_lt]) and the truncated-subtraction bridge [leq_subCr]. *)
Definition circ_dist (p a b : nat) : nat :=
  minn (absz (Posz a - Posz b)) (p - absz (Posz a - Posz b))%N.

Definition pq_colouring_cyc (V : Type) (adj : V -> V -> bool) (p q : nat) (c : V -> nat) : Prop :=
  (forall v, (c v < p)%N) /\
  (forall u v, adj u v -> (q <= circ_dist p (c u) (c v))%N).

(** A linear colour distance between two colours in [{0,…,p-1}] stays [< p]. *)
Lemma absz_sub_lt (p a b : nat) : (a < p)%N -> (b < p)%N ->
  (absz (Posz a - Posz b) < p)%N.
Proof.
move=> ap bp; case: (leqP a b) => [ab | /ltnW ba].
- have -> : absz (Posz a - Posz b) = (b - a)%N.
    by rewrite -opprB abszN subzn // absz_nat.
  exact: leq_ltn_trans (leq_subr a b) bp.
- have -> : absz (Posz a - Posz b) = (a - b)%N.
    by rewrite subzn // absz_nat.
  exact: leq_ltn_trans (leq_subr b a) ap.
Qed.

(** The per-edge kernel: for a distance [d <= p] with [q <= p], the two-sided band
    is exactly the min-based cyclic lower bound. *)
Lemma pq_band_min (p q d : nat) : (d <= p)%N -> (q <= p)%N ->
  (((q <= d)%N /\ (d <= p - q)%N) <-> (q <= minn d (p - d))%N).
Proof.
move=> dp qp; rewrite leq_min (leq_subCr qp dp).
by split=> [[-> ->] // | /andP[-> ->]].
Qed.

Lemma pq_colouring_cycE (V : Type) (adj : V -> V -> bool) (p q : nat) (c : V -> nat) :
  pq_colouring adj p q c <-> pq_colouring_cyc adj p q c.
Proof.
rewrite /pq_colouring /pq_colouring_cyc /circ_dist.
split.
- move=> [cb Hedge]; split; first exact: cb.
  move=> u v uv.
  have du : (absz (Posz (c u) - Posz (c v)) <= p)%N.
    by apply/ltnW/absz_sub_lt; apply: cb.
  have [qd _] := Hedge u v uv.
  have qp : (q <= p)%N by exact: leq_trans qd du.
  by apply: (proj1 (pq_band_min du qp)); exact: Hedge.
- move=> [cb Hedge]; split; first exact: cb.
  move=> u v uv.
  have du : (absz (Posz (c u) - Posz (c v)) <= p)%N.
    by apply/ltnW/absz_sub_lt; apply: cb.
  have qp : (q <= p)%N.
    apply: leq_trans (Hedge u v uv) _.
    exact: leq_trans (geq_minl _ _) du.
  by apply: (proj2 (pq_band_min du qp)); exact: Hedge.
Qed.
