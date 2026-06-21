(** * Digraph.conjectures.grounding_degreewidth_c3 — the marquee non-transitive case

    Δ*(C₃) = 1 and has_LFO(C₃): the degreewidth and linear-forest-ordering of the directed
    triangle.  This is the non-transitive companion to pass-1 [grounding_fas_unvd.v] (which
    grounds the TRANSITIVE Δ*(TTₙ) = 0 / has_LFO(TTₙ) via the edgeless back-arc graph).  Here
    the optimal order leaves exactly ONE back-arc (the cyclic arc 2→0 under the identity
    order 0≺1≺2), so the backedge graph is a single edge {0,2} — a linear forest of
    degreewidth 1.

    The two headline results:
      - [Delta_star_C3]  : Δ*(C₃) = 1   (degreewidth of the directed triangle);
      - [has_LFO_C3]     : has_LFO(C₃)  (its single-back-arc order is a linear forest).

    En route we prove a reusable general lemma:
      - [sdeg_le1_is_forest] : a simple graph of maximum degree ≤ 1 (a matching) is a forest.

    Toolchain: C₃ = ℤ₃ with arc u→v ⟺ v = u+1; the three arcs and their absences come from
    [arcC3E] + tournament asymmetry/irreflexivity (no ad-hoc ℤ₃ inequalities); the identity
    order's [ltp] reduces to the ordinal value order ([ltp1_C3]); the backedge graph is then
    characterized exactly ([backedge1E]). *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_fingroup all_algebra.
From Digraph Require Import prelude interop_graph_theory digraph oriented dipath.
From Digraph Require Import tournament order.
From Digraph Require Import path_fas.
Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** C₃ = ℤ₃: the identity order, the three arcs, and the arc table *)

(** Under the identity permutation the order [ltp] is the ordinal-value order. *)
Lemma ltp1_C3 (u v : C3) : ltp (1%g : {perm C3}) u v = (val u < val v)%N.
Proof. by rewrite /ltp !perm1 !enum_rank_ord. Qed.

(** 1+1+1 = 0 in ℤ₃. *)
Lemma C3_111 : (1 + 1 + 1 = 0 :> C3)%R.
Proof. by apply: val_inj. Qed.

(** The three directed-triangle arcs. *)
Lemma arc01 : (0%R : C3) --> 1%R.            Proof. by rewrite arcC3E add0r. Qed.
Lemma arc12 : (1%R : C3) --> (1 + 1)%R.       Proof. by rewrite arcC3E. Qed.
Lemma arc20 : ((1 + 1)%R : C3) --> 0%R.       Proof. by rewrite arcC3E -C3_111. Qed.

(** Enumeration of ℤ₃ by element. *)
Lemma C3_cases (u : C3) : [\/ u = 0%R, u = 1%R | u = (1 + 1)%R].
Proof.
by case: u => -[|[|[|//]]] iu; [apply: Or31|apply: Or32|apply: Or33]; apply: val_inj.
Qed.

(** Pairwise distinctness (from [arc_neq]) and the missing arcs (from tournament
    asymmetry [arc_asym]) — no fresh ℤ₃ arithmetic needed. *)
Lemma C3_01_neq : (0%R : C3) != 1%R.          Proof. exact: arc_neq arc01. Qed.
Lemma C3_12_neq : (1%R : C3) != (1 + 1)%R.     Proof. exact: arc_neq arc12. Qed.
Lemma C3_20_neq : ((1 + 1)%R : C3) != 0%R.     Proof. exact: arc_neq arc20. Qed.
Lemma C3_10_neq : (1%R : C3) != 0%R.           Proof. rewrite eq_sym; exact: C3_01_neq. Qed.
Lemma C3_21_neq : ((1 + 1)%R : C3) != 1%R.      Proof. rewrite eq_sym; exact: C3_12_neq. Qed.
Lemma C3_02_neq : (0%R : C3) != (1 + 1)%R.      Proof. rewrite eq_sym; exact: C3_20_neq. Qed.
Lemma narc10 : ~~ ((1%R : C3) --> 0%R).           Proof. exact: arc_asym arc01. Qed.
Lemma narc21 : ~~ (((1 + 1)%R : C3) --> 1%R).     Proof. exact: arc_asym arc12. Qed.
Lemma narc02 : ~~ ((0%R : C3) --> (1 + 1)%R).     Proof. exact: arc_asym arc20. Qed.

Lemma val0 : val (0%R : C3) = 0%N.        Proof. by []. Qed.
Lemma val1 : val (1%R : C3) = 1%N.        Proof. by []. Qed.
Lemma val2 : val ((1 + 1)%R : C3) = 2%N.  Proof. by []. Qed.

(** ** The backedge graph under the identity order is the single edge {0, 1+1} *)
Lemma backedge1E (u w : C3) :
  ((u : backedge (1%g : {perm C3})) -- w) =
  ((u == 0%R) && (w == (1 + 1)%R)) || ((u == (1 + 1)%R) && (w == 0%R)).
Proof.
rewrite backedgeE !ltp1_C3.
case: (C3_cases u) => ->; case: (C3_cases w) => ->;
  rewrite ?val0 ?val1 ?val2 ?arc01 ?arc12 ?arc20
    ?(negbTE narc10) ?(negbTE narc21) ?(negbTE narc02)
    ?eqxx ?(negbTE C3_01_neq) ?(negbTE C3_10_neq) ?(negbTE C3_12_neq)
    ?(negbTE C3_21_neq) ?(negbTE C3_20_neq) ?(negbTE C3_02_neq) //=.
Qed.

(** ** Δ*(C₃) = 1 *)

(** Lower bound: every order leaves a back-arc.  If the backedge graph were edgeless, every
    arc would point forward ([edgeless_arc_fwd]); but the three C₃ arcs cannot all point
    forward (0≺1≺2≺0 contradicts antisymmetry of the order). *)
Lemma edgeless_arc_fwd (T : tournament) (q : {perm T}) :
  (forall u v : backedge q, ~~ (u -- v)) -> forall a b : T, (a --> b) -> ltp q a b.
Proof.
move=> edg a b ab.
have [//|lba] := orP (ltp_total q (arc_neq ab)).
by move: (edg a b); rewrite backedgeE lba ab orbT.
Qed.

Lemma maxbackdeg_C3_ge1 (q : {perm C3}) : (1 <= maxbackdeg q)%N.
Proof.
rewrite leqNgt; apply/negP; rewrite ltnS leqn0 => /eqP m0.
have edg : forall u v : backedge q, ~~ (u -- v).
  move=> u v; apply/negP => uv.
  have h1 : (1 <= backdeg q u)%N.
    by rewrite /backdeg /sdeg card_gt0; apply/set0Pn; exists v; rewrite inE.
  have hle : (backdeg q u <= maxbackdeg q)%N by rewrite /maxbackdeg; exact: leq_bigmax.
  by move: hle; rewrite m0 leqn0 (gtn_eqF h1).
have f01 := edgeless_arc_fwd edg arc01.
have f12 := edgeless_arc_fwd edg arc12.
have f20 := edgeless_arc_fwd edg arc20.
by have := ltp_asym (ltp_trans f01 f12); rewrite f20.
Qed.

(** Upper bound: under the identity order every vertex has back-degree ≤ 1. *)
Lemma backdeg1_le1 (v : C3) : (backdeg (1%g : {perm C3}) v <= 1)%N.
Proof.
rewrite /backdeg /sdeg; apply/card_le1_eqP => w1 w2.
rewrite !inE !backedge1E.
case: (C3_cases v) => ->.
- by rewrite eqxx (negbTE C3_02_neq) /= !orbF => /eqP-> /eqP->.
- by rewrite (negbTE C3_10_neq) (negbTE C3_12_neq) /=.
- by rewrite (negbTE C3_20_neq) eqxx /= => /eqP-> /eqP->.
Qed.

Lemma maxbackdeg1_C3_le1 : (maxbackdeg (1%g : {perm C3}) <= 1)%N.
Proof. by apply: maxbackdeg_leP => v; exact: backdeg1_le1. Qed.

(** GROUNDING (headline): the degreewidth of the directed triangle is 1.
    (Davot–Isenmann–Roy–Thiebaut, arXiv:2212.06007 — the smallest non-sparse tournament.) *)
Theorem Delta_star_C3 : Delta_star C3 = 1%N.
Proof.
apply/eqP; rewrite eqn_leq; apply/andP; split.
- by apply: (leq_trans (Delta_star_min (1%g : {perm C3}))); exact: maxbackdeg1_C3_le1.
- by have [p ->] := Delta_star_witness C3; exact: maxbackdeg_C3_ge1.
Qed.

(** ** has_LFO(C₃) via "max degree ≤ 1 ⟹ forest" *)

(** Two neighbours of a degree-≤1 vertex coincide. *)
Lemma deg1_uniq_nb (G : sgraph) (deg1 : forall x : G, (sdeg x <= 1)%N) (z a b : G) :
  z -- a -> z -- b -> a = b.
Proof. by move=> za zb; apply: (card_le1_eqP (deg1 z)); rewrite inE. Qed.

(** In a degree-≤1 graph an irredundant path is a single edge (when its endpoints differ):
    after the first edge x→z, vertex z's only other neighbour would have to be x, already
    visited — so the path stops at z = y. *)
Lemma deg1_irred_xy (G : sgraph) (deg1 : forall x : G, (sdeg x <= 1)%N)
    (x y : G) (p : Path x y) (xy : x != y) :
  irred p -> exists e : x -- y, p = edgep e.
Proof.
move=> Ip.
case: (splitL p xy) => z [xz] [p'] [defp _].
move: Ip; rewrite defp irred_edgeL => /andP[xNp' Ip'].
have [zy|zNy] := eqVneq z y.
  by subst z; exists xz; rewrite (irredxx Ip') pcat_idR.
exfalso.
case: (splitL p' zNy) => w [zw] [p''] [defp' _].
move: (xz); rewrite sg_sym => zx.
have xw : x = w by apply: (deg1_uniq_nb deg1 zx zw).
move/negP: xNp'; apply.
by rewrite defp' mem_pcat mem_edgep xw eqxx !orbT.
Qed.

(** GROUNDING (reusable): a simple graph of maximum degree ≤ 1 (a matching plus isolated
    vertices) is a forest — any two irredundant paths with the same endpoints coincide. *)
Lemma sdeg_le1_is_forest (G : sgraph) (deg1 : forall x : G, (sdeg x <= 1)%N) :
  is_forest [set: G].
Proof.
apply: unique_forestT => x y p q Ip Iq.
have [xy|xy] := eqVneq x y.
  by subst y; rewrite (irredxx Ip) (irredxx Iq).
have [e ->] := deg1_irred_xy deg1 xy Ip.
have [e' ->] := deg1_irred_xy deg1 xy Iq.
by rewrite (bool_irrelevance e e').
Qed.

(** The identity-order backedge graph of C₃ is a linear forest (one edge, all degrees ≤ 1). *)
Lemma linear_forest_backedge1_C3 : linear_forest (backedge (1%g : {perm C3})).
Proof.
split.
- by apply: sdeg_le1_is_forest => x; exact: backdeg1_le1.
- by move=> x; apply: (leq_trans (backdeg1_le1 x)).
Qed.

(** GROUNDING (headline): the directed triangle has a linear-forest ordering. *)
Theorem has_LFO_C3 : has_LFO C3.
Proof. by exists (1%g : {perm C3}); exact: linear_forest_backedge1_C3. Qed.

(** Consistency cross-check: [has_LFO_C3] forces Δ*(C₃) ≤ 2 via the proved reduction
    [has_LFO_Delta_star_le2], in agreement with the exact value [Delta_star_C3] = 1. *)
Lemma Delta_star_C3_le2_via_LFO : (Delta_star C3 <= 2)%N.
Proof. exact: has_LFO_Delta_star_le2 has_LFO_C3. Qed.
