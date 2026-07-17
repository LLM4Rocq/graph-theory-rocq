(** * Chromatic.conjectures.X160 -- v2 density-zero constricting set row *)

From GTBase Require Export base.
From Chromatic.conjectures Require Import X3.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X160 vocabulary ***********************************************)

Definition x160_count_up_to (F : nat -> bool) (n : nat) : nat :=
  #|[set i : 'I_n | F ((val i).+1)]|.

Definition x160_density_zero (F : nat -> bool) : Prop :=
  forall eps_num eps_den : nat,
    0 < eps_num ->
    0 < eps_den ->
    exists N : nat,
      forall n : nat,
        N <= n ->
        eps_den * x160_count_up_to F n <= eps_num * n.

(** ** X160 statements *****************************************************)

(** Problem 1.6 asks whether an infinite constricting set of positive integers
    can have asymptotic density zero.  Reuses X3's audited constricting-set
    vocabulary. *)
Definition density_zero_constricting_set_statement : Prop :=
  exists F : nat -> bool,
    [/\ x3_positive_integer_set (fun n : nat => F n),
        x3_infinite_integer_set (fun n : nat => F n),
        x3_constricting (fun n : nat => F n) &
        x160_density_zero F].
