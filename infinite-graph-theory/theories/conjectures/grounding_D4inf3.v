(** * Grounding for the ends rows (the ends/ray vocabulary has content). *)

From GTBase Require Export base.
From Infinite Require Import foundations.igraph conjectures.D4inf3.
From mathcomp Require Import all_boot.
From mathcomp Require Import all_algebra.
Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** [reachP] is reflexive on its predicate, so [end_equiv]'s in-component walks
    are non-trivial (a vertex reaches itself). *)
Lemma reachP_refl (G : iGraph) (P : iV G -> Prop) (x : iV G) :
  P x -> reachP P x x.
Proof. exact: reachP0. Qed.

(** A concrete RAY exists (so [ray]/[wray] are non-vacuous): on [Komega] the
    identity sequence [0,1,2,…] is a ray (injective; consecutive vertices
    distinct, hence adjacent). *)
Lemma ray_Komega : ray (G := Komega) id.
Proof.
split; first exact: inj_id.
by move=> n /= H; move: (ltn_eqF (ltnSn n)); rewrite -H eqxx.
Qed.

(** [same_start] and [disjoint_rays] are a genuine equivalence-flavoured / apartness
    relation on families: [same_start] is reflexive, and disjointness is about
    distinct indices only. *)
Lemma same_start_refl (G : iGraph) (K : nat -> nat -> iV G) : same_start K K.
Proof. by split=> i; exists i. Qed.

(** [devours] is inhabited as a shape: the family that repeats [r0] devours the
    end whenever every ω-ray meets [r0] — witnessing the predicate is not
    vacuously false-typed. *)
Lemma devours_selfrepeat (G : iGraph) (r0 : nat -> iV G) :
  (forall r, wray r0 r -> exists n m, r n = r0 m) ->
  devours r0 (fun _ => r0).
Proof. by move=> H r /H [n [m E]]; exists 0, n, m. Qed.

(** The double-ray vocabulary of [uniquely_hamiltonian] has a real carrier: the
    integer line [zline] (vertices [int]; [m ~ n] iff they differ by 1) is a
    genuine [iGraph], and the identity sequence [0,±1,±2,…] is a SPANNING DOUBLE
    RAY on it — grounding both [dray] (injective, consecutive-adjacent) and
    [spanning_dray] (every vertex is hit).  So [spanning_dray] is not vacuous. *)
Definition zadj (m n : int) : Prop := (n = m + 1)%R \/ (m = n + 1)%R.

Lemma zadj_sym : irel_sym zadj.
Proof. by move=> x y [E|E]; [right|left]. Qed.

Lemma zadj_irr : irel_irr zadj.
Proof.
move=> x [] /eqP; rewrite -subr_eq0 opprD addrA subrr add0r oppr_eq0 oner_eq0 //.
Qed.

Definition zline : iGraph := Build_iGraph zadj_sym zadj_irr.

Lemma dray_spanning_zline : spanning_dray (G := zline) id.
Proof.
split; last by move=> x; exists x.
split; first exact: inj_id.
by move=> n; left.
Qed.

(** [same_circle] (the "unique up to edge set" relation at the heart of
    [uniquely_hamiltonian]) is reflexive: every double ray has the same edge set
    as itself. *)
Lemma same_circle_refl (G : iGraph) (d : int -> iV G) : same_circle d d.
Proof. by move=> x y; split. Qed.
