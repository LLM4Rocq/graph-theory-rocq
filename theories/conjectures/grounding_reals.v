(** * Digraph.conjectures.grounding_reals — GROUNDING of [reals_growth.v]

    Faithfulness check for the self-contained Landau machinery (P8) of
    [reals_growth.v]: [is_BigO] / [is_BigOmega] / [is_Theta] over real
    sequences [nat -> R], plus the [env_a] / [env_t] growth envelopes.

    A predicate claiming to be "f = Θ(g)" is only meaningful if it satisfies
    the TEXTBOOK Landau algebra: Θ is an EQUIVALENCE RELATION (reflexive,
    symmetric, transitive), Big-O is a PREORDER (reflexive, transitive), Θ
    refines into the two one-sided envelopes, and a constant multiple is
    Θ-equivalent.  These are exactly the properties any correct Θ/O definition
    must satisfy (Cormen–Leiserson–Rivest–Stein, *Introduction to Algorithms*,
    Ch. 3 "Growth of Functions"; Knuth, *TAOCP* Vol. 1 §1.2.11).  We prove them
    all by Qed against the COMMITTED [reals_growth.v] definitions.

    We also ground the envelopes [env_a n = √(n·ln n)] and
    [env_t n = √(n / ln n)]: for [n ≥ 2] both are strictly positive (a √ of a
    positive real is positive, and [ln(INR n) > 0] since [INR n ≥ 2 > 1]).  An
    extremal-function envelope that were ≤ 0 on an unbounded set could not be a
    Θ-tight bound on a positive combinatorial quantity, so positivity is the
    minimal sanity any growth envelope must pass.

    RED-FLAG WATCH: if [is_Theta] were reflexive-broken or symmetric-broken, the
    Θ-conjectures of [reals_growth.v] would be mis-encoded.  Both hold (Qed). *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude interop_graph_theory digraph oriented tournament dipath.
From Digraph Require Import dichromatic heroes.
From Digraph Require Import chi_bounded sad unvd reals_growth.
From Stdlib Require Import Reals Lra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope R_scope.
Delimit Scope nat_scope with N.

(** ** Big-O is a PREORDER (reflexive + transitive)

    Textbook: f = O(f) (with constant 1), and O composes (CLRS Ch. 3). *)

Theorem is_BigO_refl (f : nat -> R) : is_BigO f f.
Proof.
exists 1, 0%N; split; first by lra.
by move=> n _; rewrite Rmult_1_l; apply: Rle_refl.
Qed.

Theorem is_BigO_trans (f g h : nat -> R) :
  is_BigO f g -> is_BigO g h -> is_BigO f h.
Proof.
move=> [c1 [N1 [Pc1 H1]]] [c2 [N2 [Pc2 H2]]].
exists (c1 * c2), (maxn N1 N2); split; first by apply: Rmult_lt_0_compat.
move=> n Nn.
have N1n : (N1 <= n)%N by apply: leq_trans (leq_maxl _ _) Nn.
have N2n : (N2 <= n)%N by apply: leq_trans (leq_maxr _ _) Nn.
apply: (Rle_trans _ (c1 * g n)); first exact: H1.
rewrite Rmult_assoc; apply: Rmult_le_compat_l; first exact: Rlt_le.
exact: H2.
Qed.

(** ** Big-Omega is a PREORDER too (used for the Θ-equivalence). *)

Theorem is_BigOmega_refl (f : nat -> R) : is_BigOmega f f.
Proof.
exists 1, 0%N; split; first by lra.
by move=> n _; rewrite Rmult_1_l; apply: Rle_refl.
Qed.

Theorem is_BigOmega_trans (f g h : nat -> R) :
  is_BigOmega f g -> is_BigOmega g h -> is_BigOmega f h.
Proof.
move=> [c1 [N1 [Pc1 H1]]] [c2 [N2 [Pc2 H2]]].
exists (c1 * c2), (maxn N1 N2); split; first by apply: Rmult_lt_0_compat.
move=> n Nn.
have N1n : (N1 <= n)%N by apply: leq_trans (leq_maxl _ _) Nn.
have N2n : (N2 <= n)%N by apply: leq_trans (leq_maxr _ _) Nn.
apply: (Rle_trans _ (c1 * g n)); last exact: H1.
rewrite Rmult_assoc; apply: Rmult_le_compat_l; first exact: Rlt_le.
exact: H2.
Qed.

(** ** Θ is an EQUIVALENCE RELATION

    The defining textbook property of Θ.  RED-FLAG check: if EITHER reflexivity
    OR symmetry failed, [reals_growth.v]'s [is_Theta] would not encode
    "asymptotically tight bound" and the Θ-conjectures would be mis-stated. *)

Theorem is_Theta_refl (f : nat -> R) : is_Theta f f.
Proof.
exists 1, 1, 0%N; split; [lra | lra |].
by move=> n _; rewrite Rmult_1_l; split; apply: Rle_refl.
Qed.

Theorem is_Theta_sym (f g : nat -> R) : is_Theta f g -> is_Theta g f.
Proof.
move=> [c1 [c2 [N [Pc1 Pc2 H]]]].
(* From  c1 g <= f <= c2 g  derive  (1/c2) f <= g <= (1/c1) f. *)
exists (/ c2), (/ c1), N; split.
- by apply: Rinv_0_lt_compat.
- by apply: Rinv_0_lt_compat.
have c2n0 : c2 <> 0 by apply: Rgt_not_eq.
have c1n0 : c1 <> 0 by apply: Rgt_not_eq.
move=> n Nn; have [Hlo Hhi] := H n Nn; split.
- (* /c2 * f n <= g n   from   f n <= c2 * g n *)
  apply: (Rmult_le_reg_l c2) => //.
  rewrite -Rmult_assoc Rinv_r // Rmult_1_l.
  exact: Hhi.
- (* g n <= /c1 * f n   from   c1 * g n <= f n *)
  apply: (Rmult_le_reg_l c1) => //.
  rewrite -Rmult_assoc Rinv_r // Rmult_1_l.
  exact: Hlo.
Qed.

Theorem is_Theta_trans (f g h : nat -> R) :
  is_Theta f g -> is_Theta g h -> is_Theta f h.
Proof.
move=> Tfg Tgh.
apply: BigO_BigOmega_Theta.
- apply: (is_BigO_trans (g := g)).
  + exact: is_Theta_BigO Tfg.
  + exact: is_Theta_BigO Tgh.
- apply: (is_BigOmega_trans (g := g)).
  + exact: is_Theta_BigOmega Tfg.
  + exact: is_Theta_BigOmega Tgh.
Qed.

(** ** Θ refines into the two one-sided envelopes (sanity: O and Ω both hold). *)

Theorem is_Theta_BigO_BigOmega (f g : nat -> R) :
  is_Theta f g -> is_BigO f g /\ is_BigOmega f g.
Proof. by move=> T; split; [exact: is_Theta_BigO | exact: is_Theta_BigOmega]. Qed.

(** ** A constant multiple is Θ-equivalent: [2·f = Θ(f)]

    Textbook: constant factors are absorbed by Θ (CLRS Ch. 3). *)

Theorem is_Theta_const_mul (f : nat -> R) :
  is_Theta (fun n => 2 * f n) f.
Proof.
exists 2, 2, 0%N; split; [lra | lra |].
by move=> n _; split; apply: Rle_refl.
Qed.

(** More generally, ANY positive constant multiple is Θ. *)
Theorem is_Theta_scal (c : R) (f : nat -> R) :
  0 < c -> is_Theta (fun n => c * f n) f.
Proof.
move=> Pc; exists c, c, 0%N; split; [done | done |].
by move=> n _; split; apply: Rle_refl.
Qed.

(** ** Envelope positivity (n ≥ 2)

    For [n ≥ 2], [INR n ≥ 2 > 1], hence [ln(INR n) > ln 1 = 0]; then
    [env_a n = √(n·ln n) > 0] and [env_t n = √(n / ln n) > 0]. *)

Lemma INR_ge2 (n : nat) : (2 <= n)%N -> 2 <= INR n.
Proof.
move=> Hn; have H := le_INR _ _ (elimT leP Hn).
by move: H; rewrite (_ : INR 2 = 2) //=; lra.
Qed.

Lemma ln_INR_pos (n : nat) : (2 <= n)%N -> 0 < ln (INR n).
Proof.
move=> Hn; have H2 := INR_ge2 Hn.
rewrite -ln_1; apply: ln_increasing; lra.
Qed.

Theorem env_a_pos (n : nat) : (2 <= n)%N -> 0 < env_a n.
Proof.
move=> Hn; rewrite /env_a; apply: sqrt_lt_R0.
apply: Rmult_lt_0_compat; last exact: ln_INR_pos.
have H2 := INR_ge2 Hn; lra.
Qed.

Theorem env_t_pos (n : nat) : (2 <= n)%N -> 0 < env_t n.
Proof.
move=> Hn; rewrite /env_t; apply: sqrt_lt_R0.
apply: Rdiv_lt_0_compat; last exact: ln_INR_pos.
have H2 := INR_ge2 Hn; lra.
Qed.

(** ** The envelopes ARE Θ of themselves (closing the loop with the conjectures)

    Trivial but exercises [is_Theta] on the actual [reals_growth.v] envelopes. *)
Theorem env_a_Theta_self : is_Theta env_a env_a. Proof. exact: is_Theta_refl. Qed.
Theorem env_t_Theta_self : is_Theta env_t env_t. Proof. exact: is_Theta_refl. Qed.

(** ** log2 base sanity: [log2 2 = 1] and [log2] is the [ln]/[ln 2] ratio.

    Grounds the EC-log threshold's [log2] used in [ec_log_statement]: the base-2
    log of its base is 1 (a definitional sanity any [log2] must pass). *)
Theorem log2_2 : log2 2 = 1.
Proof.
rewrite /log2; apply: Rinv_r.
by apply: Rgt_not_eq; have := ln_lt_2; lra.
Qed.

Theorem log2_pos_gt1 (x : R) : 1 < x -> 0 < log2 x.
Proof.
move=> Hx; rewrite /log2; apply: Rdiv_lt_0_compat.
- by rewrite -ln_1; apply: ln_increasing; lra.
- by have := ln_lt_2; lra.
Qed.
