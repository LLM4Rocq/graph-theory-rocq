(** * Digraph.conjectures.grounding_dichromatic_cycle — χ⃗(directed n-cycle) = 2

    The dichromatic number of the directed n-cycle is exactly 2 (for n ≥ 2): it is not
    acyclic (χ⃗ ≥ 2) yet 2-dicolourable (χ⃗ ≤ 2).  This extends the keystone grounding
    [grounding_dichromatic.v] (which fixes χ⃗(C₃) = 2) to the whole family of directed
    cycles, and — at n = 4 — exhibits the canonical TIGHTNESS witness for Conjecture 6.2
    [grounding_heroes_dichotomy.v]: the directed C₄ is oriented, C₃-free and S₂⁺-free, so it
    lies in Forb_ind(digon, C₃, S₂⁺), and χ⃗(C₄) = 2 shows the conjectured bound "≤ 2" is
    ATTAINED (the previously-grounded edgeless witness only gives the trivial ≤ 2).

    The reusable engine is [acyclicb_potential]: a digraph carrying a strictly-increasing
    integer potential along its arcs is acyclic.  The 2-colouring sets one vertex apart;
    on each colour class the vertex value strictly increases along arcs (the only
    value-decreasing arc is the wrap n−1 → 0, which crosses the two classes), so both
    classes are acyclic.  Non-acyclicity uses that the successor map is a permutation, so
    the cycle is strongly connected ([fconnect]).

    NB: the directed cycle is re-defined here (identical to [two_extremal_glue.di_cycle]:
    ['I_n] with arc i → (i+1) mod n) to avoid that module's heavy [generic_quotient]
    dependency. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_fingroup all_algebra.
From Digraph Require Import prelude digraph dipath tournament.
From Digraph Require Import dichromatic chi_bounded.
From Digraph Require Import grounding_dichromatic.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Reusable: a strictly-increasing potential along arcs forces acyclicity *)
Lemma acyclicb_potential (D : diGraphType) (phi : D -> nat) :
  (forall x y : D, x --> y -> (phi x < phi y)%N) -> acyclicb D.
Proof.
move=> inc; apply/forallP=> v; apply/forallP=> w; apply/implyP=> vw.
apply/negP=> /connectP[s pth lst].
suff le_wv : (phi w <= phi v)%N by move: le_wv; rewrite leqNgt (inc _ _ vw).
rewrite lst; elim: s w pth {vw lst} => [|b t IH] w /=; first by rewrite leqnn.
by case/andP=> wb pt; apply: leq_trans (ltnW (inc _ _ wb)) (IH b pt).
Qed.

(** ** The directed n-cycle ['I_n] with arc i → (i+1) mod n *)
Section DCycDef.
Variable n : nat.
Definition dcyc_rel (x y : 'I_n) : bool := val y == (val x).+1 %% n.
Definition dcyc : Type := 'I_n.
HB.instance Definition _ := Finite.on dcyc.
HB.instance Definition _ := HasArc.Build dcyc dcyc_rel.
Definition dcycle : diGraphType := dcyc.
Lemma dcycle_arcE (x y : dcycle) : (x --> y) = (val y == (val x).+1 %% n).
Proof. by []. Qed.
End DCycDef.

Section DCycChi.
Variable n : nat.
Hypothesis n2 : (2 <= n)%N.

(** An arc landing on a nonzero vertex strictly increases the value (no wrap). *)
Lemma dcyc_arc_noWrap (x y : dcycle n) : (x --> y) -> (val y != 0)%N -> (val x < val y)%N.
Proof.
rewrite dcycle_arcE => /eqP-> nz.
have xn : (val x < n)%N := ltn_ord x.
case: (ltngtP (val x).+1 n) => [lt|gt|e].
- by rewrite modn_small // ltnSn.
- by move: gt; rewrite ltnS leqNgt xn.
- by exfalso; move: nz; rewrite e modnn eqxx.
Qed.

(** ** Upper bound: 2-dicolourable (set vertex 0 apart; each class has increasing value) *)
Lemma ord01_neq : (ord0 : 'I_2) != ord_max.
Proof. by rewrite -(inj_eq val_inj). Qed.

Lemma dcycle_2dicol : dicolorableb (dcycle n) 2.
Proof.
apply/existsP.
exists [ffun v : dcycle n => if val v == 0 then (ord_max : 'I_2) else ord0].
apply/forallP=> i.
set col := [ffun v : dcycle n => if val v == 0 then (ord_max : 'I_2) else ord0].
set S := [set v | col v == i].
apply: (acyclicb_potential (phi := fun x : induced_digraph S => val (val x))).
move=> x y; rewrite sub_arcE => xy.
have yS : val y \in S := valP y.
have xS : val x \in S := valP x.
have [yz|ynz] := eqVneq (val (val y)) 0%N; last by exact: dcyc_arc_noWrap xy ynz.
exfalso.
have vx_ne0 : (val (val x) != 0)%N.
  apply/negP=> /eqP vx0; move: xy.
  by rewrite dcycle_arcE yz vx0 /= (modn_small n2).
move: yS xS; rewrite !inE /col !ffunE yz eqxx (negbTE vx_ne0) /= => /eqP <-.
by rewrite (negbTE ord01_neq).
Qed.

(** ** Lower bound: not acyclic — the cycle's successor map is a permutation, so it is
       strongly connected and every vertex lies on a directed cycle. *)
Let n0 : (0 < n)%N. Proof. exact: leq_trans (ltn0Sn 1) n2. Qed.
Definition succ (x : dcycle n) : dcycle n := Ordinal (ltn_pmod (val x).+1 n0).
Lemma arc_succ (x y : dcycle n) : (x --> y) = (y == succ x).
Proof. by rewrite dcycle_arcE -(inj_eq val_inj). Qed.
Lemma succ_inj : injective succ.
Proof.
move=> x y /(f_equal val) /=; rewrite -addn1 -[(val y).+1]addn1.
move/eqP; rewrite eqn_modDr => /eqP.
by rewrite (modn_small (ltn_ord x)) (modn_small (ltn_ord y)); exact: val_inj.
Qed.
Lemma connect_arc_succ (x y : dcycle n) : connect arc x y = fconnect succ x y.
Proof. by apply: eq_connect => u v; rewrite arc_succ. Qed.

Lemma dcycle_not_acyclic : ~~ acyclicb (dcycle n).
Proof.
pose v0 : dcycle n := Ordinal n0.
apply/forallPn; exists v0; rewrite negb_forall; apply/existsP; exists (succ v0).
rewrite negb_imply negbK; apply/andP; split.
- by rewrite arc_succ.
- by rewrite connect_arc_succ (fconnect_sym succ_inj); exact: fconnect1.
Qed.

(** ** χ⃗(dcycle n) = 2 *)
Theorem not_dicolorableb_dcycle_1 : ~~ dicolorableb (dcycle n) 1.
Proof. by rewrite dicolorableb1; exact: dcycle_not_acyclic. Qed.

(** GROUNDING (headline): the directed n-cycle has dichromatic number exactly 2 —
    not 1-dicolourable (χ⃗ ≥ 2) and 2-dicolourable (χ⃗ ≤ 2). *)
Theorem chi_dcycle_eq2 : ~~ dicolorableb (dcycle n) 1 /\ dicolorableb (dcycle n) 2.
Proof. by split; [exact: not_dicolorableb_dcycle_1 | exact: dcycle_2dicol]. Qed.

End DCycChi.

(** χ⃗ of the directed C₄ = 2: the canonical TIGHTNESS witness for Conjecture 6.2
    (Forb_ind(digon, C₃, S₂⁺) is χ⃗ ≤ 2, attained by the oriented, C₃-free, S₂⁺-free C₄). *)
Corollary chi_dcycle_C4 : ~~ dicolorableb (dcycle 4) 1 /\ dicolorableb (dcycle 4) 2.
Proof. exact: chi_dcycle_eq2. Qed.

(** The directed 4-cycle has 4 vertices. *)
Lemma card_dc4 : #|{: dcycle 4}| = 4.
Proof. by rewrite card_ord. Qed.

(** GROUNDING (chi_bounded.v, tvec_core "attained" clause): the directed 4-cycle
    is a genuine member of the oriented, underlying-triangle-free class that is NOT
    1-dicolourable (its dichromatic number is 2, not 1). This gives the tfree-class
    "attained" existential real teeth — its members are not all trivially
    1-dicolourable. It combines: (i) [oriented_dg] (no digons, by the mod-4 arc
    relation), (ii) [underlying_triangle_free] (the underlying graph is the
    undirected C₄, whose two diagonal pairs {0,2},{1,3} are non-adjacent, so no
    3-clique fits in the 4 vertices), and (iii) [~~ dicolorableb _ 1] (reusing the
    keystone [chi_dcycle_C4]). *)
Lemma dcycle4_tfree_not1 :
  oriented_dg (dcycle 4) /\ underlying_triangle_free (dcycle 4)
  /\ ~~ dicolorableb (dcycle 4) 1.
Proof.
split; last split.
- move=> u v; rewrite !dcycle_arcE.
  by case: u => -[|[|[|[|]]]] ?; case: v => -[|[|[|[|]]]] ?.
- rewrite /underlying_triangle_free /no_underlying_Kl.
  move=> [S [cardS clq]].
  pose o0 : dcycle 4 := Ordinal (isT : (0 < 4)%N).
  pose o1 : dcycle 4 := Ordinal (isT : (1 < 4)%N).
  pose o2 : dcycle 4 := Ordinal (isT : (2 < 4)%N).
  pose o3 : dcycle 4 := Ordinal (isT : (3 < 4)%N).
  have cardCS : #|~: S| = 1.
    have H := cardsC S; rewrite cardS card_dc4 in H.
    by move/eqP: H; rewrite eqn_add2l => /eqP.
  have /cards1P[z Hz] : #|~: S| == 1 by rewrite cardCS.
  have Sz : S = ~: [set z] by rewrite -Hz setCK.
  have Smem : forall a : dcycle 4, (a \in S) = (a != z).
    by move=> a; rewrite Sz !inE.
  (* clique adjacency of the underlying sgraph unfolds to [urel]; a non-adjacent
     pair inside [S] is a contradiction. *)
  have contra : forall a b : dcycle 4,
      a \in S -> b \in S -> a != b -> ~~ @urel (dcycle 4) a b -> False.
    move=> a b Ha Hb ab nadj.
    have Hadj : @urel (dcycle 4) a b := clq a b Ha Hb ab.
    by rewrite Hadj in nadj.
  (* the missing vertex [z] lies in at most one diagonal pair, so the other
     diagonal pair is entirely in [S] and is non-adjacent. *)
  have [zin|zout] := boolP (z \in [set o0; o2]).
  + have z1 : o1 != z by apply/negP => /eqP e; move: zin; rewrite -e !inE.
    have z3 : o3 != z by apply/negP => /eqP e; move: zin; rewrite -e !inE.
    apply: (contra o1 o3).
    * by rewrite Smem.
    * by rewrite Smem.
    * by [].
    * by rewrite /urel !dcycle_arcE.
  + have z0 : o0 != z by apply/negP => /eqP e; move: zout; rewrite -e !inE eqxx.
    have z2 : o2 != z by apply/negP => /eqP e; move: zout; rewrite -e !inE eqxx orbT.
    apply: (contra o0 o2).
    * by rewrite Smem.
    * by rewrite Smem.
    * by [].
    * by rewrite /urel !dcycle_arcE.
- exact: (proj1 chi_dcycle_C4).
Qed.
