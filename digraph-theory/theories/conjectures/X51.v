(** * Digraph.conjectures.X51 -- v2 majority choosability row *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph oriented.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X51 vocabulary ************************************************)

Definition x51_same_colour_outneighbours
    (D : diGraphType) (C : finType) (col : D -> C) (v : D) : nat :=
  #|[set w : D | (v --> w) && (col w == col v)]|.

Definition x51_majority_colouring
    (D : diGraphType) (C : finType) (col : D -> C) : Prop :=
  forall v : D,
    (2 * x51_same_colour_outneighbours col v <= outdeg v)%N.

Definition x51_respects_lists
    (D : diGraphType) (C : finType) (L : D -> {set C}) (col : D -> C) : Prop :=
  forall v : D, col v \in L v.

(** ** X51 statements ******************************************************)

(** arXiv:1608.03040, Open Problem 7: every digraph is majority
    c-choosable for a universal constant c. *)
Definition majority_choosable_universal_constant_statement : Prop :=
  exists c : nat,
    0 < c /\
    forall (D : diGraphType) (C : finType) (L : D -> {set C}),
      (forall v : D, c <= #|L v|) ->
      exists col : D -> C,
        x51_respects_lists L col /\
        x51_majority_colouring col.
