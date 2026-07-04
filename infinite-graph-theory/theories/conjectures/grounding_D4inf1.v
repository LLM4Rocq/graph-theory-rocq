(** * Grounding for the M1 infinite rows (the encodings have content). *)

From GTBase Require Export base.
From Infinite Require Import foundations.igraph conjectures.D4inf1.
From mathcomp Require Import all_boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** [card_le] is reflexive, and the empty predicate is ≤ anything — so the
    "at least as many" clause is a genuine cardinal comparison, not trivial. *)
Lemma card_le_refl (A : Type) (P : A -> Prop) : card_le P P.
Proof. by exists id. Qed.

Lemma card_le_empty (A B : Type) (P : A -> Prop) (Q : B -> Prop) :
  (forall x : A, ~ P x) -> card_le P Q.
Proof.
move=> hP; exists (fun s : {x | P x} => match hP (sval s) (svalP s) return {y | Q y} with end).
by move=> [x px]; case: (hP x px).
Qed.

(** The edgeless graph: a countable graph that IS unfriendly under any
    partition (both neighbourhoods empty), so the existential conclusion of
    [unfriendly_partitions_statement] is satisfiable — non-vacuous. *)
Lemma Iempty_sym : irel_sym (fun _ _ : nat => False). Proof. by move=> x y []. Qed.
Lemma Iempty_irr : irel_irr (fun _ _ : nat => False). Proof. by move=> x []. Qed.
Definition Iempty : iGraph := Build_iGraph Iempty_sym Iempty_irr.

Lemma Iempty_countable : countable_graph Iempty.
Proof. by exists id. Qed.

Lemma Iempty_unfriendly (p : iV Iempty -> bool) : unfriendly p.
Proof. by move=> x; apply: card_le_empty => w [] //. Qed.

(** But a constant partition is NOT unfriendly once there is an edge: on
    [Komega], colouring all vertices the same leaves every vertex with only
    same-class neighbours, so the guard has teeth (rules out the trivial [p]). *)
Lemma Komega_const_not_unfriendly : ~ unfriendly (G := Komega) (fun _ => true).
Proof.
move=> /(_ 0) [f _].
(* 0's same-class neighbourhood contains 1; its other-class neighbourhood is
   empty (all vertices share the class), so no injection own -> cross exists. *)
have own1 : own_nbr (G := Komega) (fun _ => true) 0 1 by split.
by case: (f (exist _ 1 own1)) => w [_ H]; apply: H.
Qed.

(** A triangle-free graph has the one-colour cover (itself), so [ctf_cover] is
    inhabited — [~ ctf_cover] in the row is a real (open) requirement. *)
Lemma ctf_cover_triangle_free (G : iGraph) :
  (~ exists x y z : iV G, iadj x y /\ iadj y z /\ iadj x z) -> ctf_cover G.
Proof.
move=> tf; exists (fun _ _ => 0); split=> // x y z axy ayz axz _ _.
by apply: tf; exists x, y, z.
Qed.

(** [K4_free] genuinely excludes the complete graph [Komega] (it has a K4), so
    the [K4_free] guard is not vacuously universal. *)
Lemma Komega_not_K4_free : ~ K4_free Komega.
Proof.
move=> H; apply: H; exists 0, 1, 2, 3.
by split.
Qed.
