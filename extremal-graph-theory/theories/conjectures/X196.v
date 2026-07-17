(** * Extremal.conjectures.X196 -- v2 Ramsey-nice infinitely often row *)

From GTBase Require Export base.
From Extremal.conjectures Require Import X195.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X196 statements *****************************************************)

(** Conjecture 1.5, the weaker Ramsey-nice sibling: every finite graph family
    containing a forest is [k]-nice for infinitely many [k]. *)
Definition ramsey_nice_forest_family_infinite_statement : Prop :=
  forall (r : nat) (Fam : 'I_r -> sgraph),
    0 < r ->
    x195_contains_forest Fam ->
    forall k0 : nat,
      exists k : nat, k0 <= k /\ x195_k_nice k Fam.
