(** * Chromatic.conjectures.X63 -- v2 two-homogeneous colouring row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X63 vocabulary ************************************************)

Definition x63_proper_colouring
    (G : sgraph) (C : finType) (col : G -> C) : Prop :=
  forall x y : G, x -- y -> col x != col y.

Definition x63_neighbour_colours
    (G : sgraph) (C : finType) (col : G -> C) (v : G) : {set C} :=
  [set c : C | [exists u : G, (u -- v) && (col u == c)]].

Definition x63_k_homogeneous_colouring (G : sgraph) (k : nat) : Prop :=
  exists (C : finType) (col : G -> C),
    x63_proper_colouring col /\
    forall v : G, #|x63_neighbour_colours col v| = k.

Definition x63_k_homogeneous_with
    (G : sgraph) (C : finType) (col : G -> C) (k : nat) : Prop :=
  x63_proper_colouring col /\
  forall v : G, #|x63_neighbour_colours col v| = k.

(** ** X63 statements ******************************************************)

(** arXiv:2511.02892, Problem 5.1: if a cubic graph admits a 2-homogeneous
    colouring, then four colours suffice. *)
Definition cubic_two_homogeneous_four_colour_statement : Prop :=
  forall G : sgraph,
    regular G 3 ->
    x63_k_homogeneous_colouring G 2 ->
    exists col : G -> 'I_4,
      x63_k_homogeneous_with col 2.
