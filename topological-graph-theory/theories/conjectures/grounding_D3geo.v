(** * Grounding for the D3 metric-geometry row (non-vacuity of the encoding). *)

From GTBase Require Export base.
From mathcomp Require Import all_algebra.
From Topological.foundations Require Import geometry.
From Topological.conjectures Require Import D3geo.
(* Re-import [all_algebra] AFTER [D3geo] to restore the numeric canonical
   structures (order / [1] on a [realFieldType]); the transitive [D3geo] import
   otherwise leaves a competing instance active and [t <= 1] fails to elaborate. *)
From mathcomp Require Import all_algebra.
Import GRing.Theory Num.Theory.
Set Implicit Arguments.
Unset Strict Implicit.
Local Open Scope ring_scope.

(** The geometric primitive has content: a non-degenerate right triangle has
    nonzero orientation ([orient_unit] in geometry.v proves it equals [1]), so
    [orient] is not the constant-zero relation — hence [between], [seg_cross] and
    [seg_meet] are all non-trivial (not silently satisfiable / silently false). *)

(** A single vertex embeds straight-line onto any point (no edges to constrain),
    so [straightline_planar] is satisfiable — the drawing predicate underlying
    [n_universal] is not vacuously false. *)
Lemma straightline_drawing_inhabited (R : realFieldType) (a : pt R) :
  straightline_planar (G := 'K_1) (fun=> a).
Proof. exact: straightline_planar_K1. Qed.

(** ============================================================================
    TECHNIQUE #3 — independent re-encoding of [between] with a proved [<->].

    [between a b c] (geometry.v) is the SIGN/BOX characterisation of "[c] lies on
    the closed segment [a,b]": collinearity ([orient a b c = 0]) together with two
    coordinate box tests [(c.i - a.i) * (c.i - b.i) <= 0].  We give the classical,
    structurally unrelated CONVEX-COMBINATION characterisation — [c] is the affine
    barycentre [a + t·(b - a)] for some parameter [t ∈ [0,1]] — and prove the two
    are equivalent over an arbitrary ordered field.

    The equivalence is genuinely non-trivial: it is NOT [by []] / definitional.
    The forward direction is a three-way case analysis (b.1 ≠ a.1 uses coordinate
    1 to solve for [t] and the collinearity equation to recover coordinate 2;
    b.1 = a.1 forces c.1 = a.1 from the box being a nonpositive square, then a
    further split on b.2); the reverse direction is a substitution followed by the
    sign identity [t·(t-1) ≤ 0 ⟺ 0 ≤ t ≤ 1].  Agreement between the two faithful
    encodings is the faithfulness evidence for [between].
    ========================================================================== *)

(** Convex-combination (affine-parameter) reading of betweenness. *)
Definition between_param (R : realFieldType) (a b c : pt R) : Prop :=
  exists t : R, [/\ 0 <= t <= 1,
     c.1 = a.1 + t * (b.1 - a.1) & c.2 = a.2 + t * (b.2 - a.2)].

(** The parameter of a convex combination lies in [[0,1]] iff [t·(t-1) ≤ 0]. *)
Lemma seg01 (R : realFieldType) (t : R) : t * (t - 1) <= 0 -> (0 <= t <= 1).
Proof.
move=> h; apply/andP; split.
- case: (lerP 0 t) => // hlt.
  move: h; rewrite (nmulr_rle0 (t - 1) hlt) subr_ge0 => h1.
  by move: (order.Order.POrderTheory.le_lt_trans h1 hlt); rewrite ltr10.
- case: (lerP t 1) => // hlt.
  have tpos : 0 < t := order.Order.POrderTheory.lt_trans ltr01 hlt.
  move: h; rewrite (pmulr_rle0 (t - 1) tpos) subr_le0 => h1.
  by move: (order.Order.POrderTheory.lt_le_trans hlt h1);
     rewrite order.Order.POrderTheory.ltxx.
Qed.

Lemma seg01_conv (R : realFieldType) (t : R) : (0 <= t <= 1) -> t * (t - 1) <= 0.
Proof. move=> /andP[t0 t1]; apply: mulr_ge0_le0 => //; by rewrite subr_le0. Qed.

(** A ratio [p/q] with a nonpositive numerator product [p·(p-q)] lands in [[0,1]]. *)
Lemma seg_ratio (R : realFieldType) (p q : R) :
  q != 0 -> p * (p - q) <= 0 -> 0 <= p / q <= 1.
Proof.
move=> qne H; apply: seg01.
have hq2 : 0 < q * q by rewrite lt0r mulf_neq0 //= -expr2 sqr_ge0.
have key : (p / q) * (p / q - 1) * (q * q) = p * (p - q).
  by rewrite mulrACA (divfK qne p) mulrBl (divfK qne p) mul1r.
by move: H; rewrite -key (pmulr_lle0 _ hq2).
Qed.

(** A box term of a genuine convex combination is nonpositive. *)
Lemma box_of_seg (R : realFieldType) (t x : R) :
  (0 <= t <= 1) -> (t * x) * ((t - 1) * x) <= 0.
Proof.
move=> H; rewrite mulrACA; apply: mulr_le0_ge0.
- exact: seg01_conv.
- by rewrite -expr2 sqr_ge0.
Qed.

(** MAIN [<->]: the sign/box encoding [between] agrees with the affine-parameter
    encoding [between_param].  Axiom-free (checked below). *)
Lemma betweenP (R : realFieldType) (a b c : pt R) :
  between a b c <-> between_param a b c.
Proof.
rewrite /between /between_param /collinear /orient; split.
{ (* forward *)
  move=> [co [box1 box2]].
  have [hb|hb] := eqVneq (b.1) (a.1).
  { (* b.1 = a.1 *)
    have hc1 : c.1 = a.1.
    { have key : (c.1 - a.1) ^+ 2 == 0.
      { rewrite order.Order.POrderTheory.eq_le sqr_ge0 andbT expr2.
        by move: box1; rewrite hb. }
      by move: key; rewrite expf_eq0 /= subr_eq0 => /eqP. }
    have [hb2|hb2] := eqVneq (b.2) (a.2).
    { have hc2 : c.2 = a.2.
      { have key : (c.2 - a.2) ^+ 2 == 0.
        { rewrite order.Order.POrderTheory.eq_le sqr_ge0 andbT expr2.
          by move: box2; rewrite hb2. }
        by move: key; rewrite expf_eq0 /= subr_eq0 => /eqP. }
      exists 0; split.
      { by rewrite order.Order.POrderTheory.lexx ler01. }
      { by rewrite hc1 mul0r addr0. }
      by rewrite hc2 mul0r addr0. }
    have vne : b.2 - a.2 != 0 by rewrite subr_eq0.
    have ecb : c.2 - b.2 = (c.2 - a.2) - (b.2 - a.2) by rewrite opprB addrA subrK.
    exists ((c.2 - a.2) / (b.2 - a.2)); split.
    { by apply: seg_ratio => //; rewrite -ecb. }
    { by rewrite hc1 hb subrr mulr0 addr0. }
    by rewrite (divfK vne (c.2 - a.2)) addrCA subrr addr0. }
  (* b.1 != a.1 *)
  have wne : b.1 - a.1 != 0 by rewrite subr_eq0.
  have ecb : c.1 - b.1 = (c.1 - a.1) - (b.1 - a.1) by rewrite opprB addrA subrK.
  have co' : (b.1 - a.1) * (c.2 - a.2) = (b.2 - a.2) * (c.1 - a.1).
  { by apply/eqP; rewrite -subr_eq0; apply/eqP. }
  have hc2 : c.2 - a.2 = (c.1 - a.1) / (b.1 - a.1) * (b.2 - a.2).
  { apply: (mulfI wne).
    by rewrite mulrA mulrCA (mulfV wne) mulr1 co' mulrC. }
  exists ((c.1 - a.1) / (b.1 - a.1)); split.
  { by apply: seg_ratio => //; rewrite -ecb. }
  { by rewrite (divfK wne (c.1 - a.1)) addrCA subrr addr0. }
  by rewrite -hc2 addrCA subrr addr0. }
(* backward *)
move=> [t [Ht e1 e2]].
have d1 : c.1 - a.1 = t * (b.1 - a.1) by rewrite e1 addrAC subrr add0r.
have d2 : c.2 - a.2 = t * (b.2 - a.2) by rewrite e2 addrAC subrr add0r.
have d1b : c.1 - b.1 = (t - 1) * (b.1 - a.1) by rewrite mulrBl mul1r -d1 opprB addrA subrK.
have d2b : c.2 - b.2 = (t - 1) * (b.2 - a.2) by rewrite mulrBl mul1r -d2 opprB addrA subrK.
split.
{ by rewrite d1 d2 mulrCA [(b.2 - a.2) * (t * (b.1 - a.1))]mulrCA
     [(b.2 - a.2) * (b.1 - a.1)]mulrC subrr. }
split.
{ by rewrite d1 d1b; apply: box_of_seg. }
by rewrite d2 d2b; apply: box_of_seg.
Qed.

Print Assumptions betweenP.
