(** * Chromatic.conjectures.X183 -- v2 d-degenerate list-flexibility row *)

From GTBase Require Export base.
From Chromatic.conjectures Require Import X132.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X183 statements *****************************************************)

(** Dvorak-Norin-Postle Problem 1: for every [d], list size [d+1] should imply
    weighted epsilon-flexibility, or at least epsilon-flexibility, on
    [d]-degenerate graphs.  The stronger weighted form is stated. *)
Definition degenerate_list_flexibility_d_plus_one_statement : Prop :=
  forall d : nat,
    exists p q : nat,
      [/\ 0 < p, p <= q &
        forall G : sgraph,
          k_degenerate G d ->
          weighted_epsilon_flexible G d.+1 p q].
