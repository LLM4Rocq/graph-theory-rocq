(** * Digraph.conjectures.X45 -- v2 majority 3-colouring row *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph oriented.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X45 vocabulary ************************************************)

Definition x45_same_colour_outneighbours
    (D : diGraphType) (col : D -> 'I_3) (v : D) : nat :=
  #|[set w : D | (v --> w) && (col w == col v)]|.

(** ** X45 statements ******************************************************)

(** arXiv:1608.03040 (Kreutzer, Oum, Seymour, van der Zypen, Wood),
    Majority 3-Colouring Conjecture: every digraph admits a 3-colouring in
    which every vertex has at most half of its out-neighbours sharing its
    colour (the majority / beta = 1/2 threshold, as in sibling X51). *)
Definition majority_three_colouring_beta_statement : Prop :=
  forall D : diGraphType,
    exists col : D -> 'I_3,
      forall v : D,
        (2 * x45_same_colour_outneighbours col v <= outdeg v)%N.
