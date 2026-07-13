(** * Digraph.conjectures.X107 -- v2 oriented Ramsey row *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph oriented tournament dichromatic.
From Digraph.conjectures Require Import X2.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X107 vocabulary ***********************************************)

Definition x107_total_degree_at_most (D : diGraphType) (Delta : nat) : Prop :=
  let indeg v := #|[set u : D | u --> v]| in
  forall v : D, outdeg v + indeg v <= Delta.

Definition x107_oriented_ramsey_at_most (H : diGraphType) (N : nat) : Prop :=
  forall T : tournament,
    N <= #|T| ->
    subdigraph_embed H T.

(** ** X107 statements *****************************************************)

(** Studies slice: Bucic-Letzter-Sudakov problem asking whether the oriented
    Ramsey number of every n-vertex acyclic digraph with maximum degree Delta
    is O_Delta(n). *)
Definition bounded_degree_acyclic_oriented_ramsey_linear_statement : Prop :=
  forall Delta : nat,
    exists C : nat,
      forall (n : nat) (H : diGraphType),
        #|H| = n ->
        acyclicb H ->
        x107_total_degree_at_most H Delta ->
        x107_oriented_ramsey_at_most H (C * n).
