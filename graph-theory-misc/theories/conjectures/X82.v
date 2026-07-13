(** * GTMisc.conjectures.X82 -- v2 outerplanar proper-orientation row *)

From GTBase Require Export base.
From GraphTheory Require Import minor.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X82 vocabulary ************************************************)

Definition x82_orientation_of (G : sgraph) (D : rel G) : Prop :=
  (forall x y : G, D x y -> x -- y) /\
  forall x y : G, x -- y -> (D x y) (+) (D y x).

Definition x82_indegree (G : sgraph) (D : rel G) (v : G) : nat :=
  #|[set u : G | D u v]|.

Definition x82_proper_orientation (G : sgraph) (D : rel G) : Prop :=
  forall x y : G, x -- y -> x82_indegree D x != x82_indegree D y.

Definition x82_proper_orientation_bound (G : sgraph) (k : nat) : Prop :=
  exists D : rel G,
    x82_orientation_of D /\
    x82_proper_orientation D /\
    forall v : G, x82_indegree D v <= k.

Definition x82_outerplanar (G : sgraph) : Prop :=
  ~ minor G 'K_4 /\ ~ minor G (KB 2 3).

(** ** X82 statements ******************************************************)

(** Studies slice: Araujo-Havet-Linhares Sales-Silva conjecture that
    outerplanar graphs have bounded proper orientation number. *)
Definition outerplanar_bounded_proper_orientation_number_statement : Prop :=
  exists C : nat,
    forall G : sgraph,
      x82_outerplanar G ->
      x82_proper_orientation_bound G C.
