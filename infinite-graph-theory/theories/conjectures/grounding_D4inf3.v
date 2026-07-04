(** * Grounding for the ends rows (the ends/ray vocabulary has content). *)

From GTBase Require Export base.
From Infinite Require Import foundations.igraph conjectures.D4inf3.
From mathcomp Require Import all_boot.

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
