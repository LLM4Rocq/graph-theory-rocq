(** * Digraph.conjectures.X52 -- v2 chromatic Mader bound row *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude interop_graph_theory digraph oriented.
From Digraph.conjectures Require Import chi_bounded X2.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X52 vocabulary ************************************************)

Definition x52_mader_chi_bound (F : diGraphType) (m : nat) : Prop :=
  forall D : diGraphType,
    (m <= χ([set: chi_bounded.underlying D]))%N ->
    contains_subdivision F D.

(** ** X52 statements ******************************************************)

(** arXiv:1610.00876, Conjecture 11: an oriented tree of order k has
    chromatic Mader threshold at most 2k-2. *)
Definition oriented_tree_mader_chi_linear_bound_statement : Prop :=
  forall (T : orientedDigraph) (k : nat),
    oriented_tree T ->
    #|T| = k ->
    x52_mader_chi_bound T (2 * k - 2).
