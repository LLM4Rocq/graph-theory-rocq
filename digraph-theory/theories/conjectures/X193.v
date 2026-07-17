(** * Digraph.conjectures.X193 -- v2 directed-triangle-free domination row *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph dipath classic_core.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X193 vocabulary ***********************************************)

Definition x193_directed_triangle_free (D : diGraphType) : Prop :=
  forall c : seq D, dicycle c -> size c != 3.

Definition x193_dominates (D : diGraphType) (S : {set D}) (v : D) : bool :=
  (v \in S) || [exists u in S, u --> v].

Definition x193_dominating_set (D : diGraphType) (S : {set D}) : Prop :=
  forall v : D, x193_dominates S v.

Definition x193_domination_number_at_most (D : diGraphType) (n : nat) : Prop :=
  exists S : {set D}, x193_dominating_set S /\ #|S| <= n.

Definition x193_independence_number (D : diGraphType) (a : nat) : Prop :=
  (exists S : {set D}, stable S /\ #|S| = a) /\
  forall S : {set D}, stable S -> #|S| <= a.

(** ** X193 statements *****************************************************)

(** Harutyunyan-Le-Newman-Thomasse Conjecture 3.5: domination number in
    directed-triangle-free digraphs is bounded polynomially in the independence
    number.  The polynomial is encoded by an existential exponent [ell]. *)
Definition directed_triangle_free_domination_polynomial_statement : Prop :=
  exists ell : nat,
    forall (D : diGraphType) (alpha : nat),
      x193_directed_triangle_free D ->
      x193_independence_number D alpha ->
      x193_domination_number_at_most D (alpha ^ ell).
