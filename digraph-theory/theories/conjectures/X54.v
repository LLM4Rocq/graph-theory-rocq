(** * Digraph.conjectures.X54 -- v2 odd directed-cycle chi-bound row *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude interop_graph_theory digraph dipath.
From Digraph.conjectures Require Import chi_bounded dichromatic.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X54 vocabulary ************************************************)

Definition x54_no_induced_odd_dicycle (D : diGraphType) : Prop :=
  ~ exists c : seq D,
      dicycle c /\ odd (size c) /\
      (forall u v : D, u \in c -> v \in c -> u --> v -> next c u = v).

(** ** X54 statements ******************************************************)

(** arXiv:2201.08204, Question 3.2: excluding induced odd directed cycles
    should chi-bound the dichromatic number by the clique number. *)
Definition odd_dicycle_free_dichromatic_chi_bound_statement : Prop :=
  exists f : nat -> nat,
    forall D : diGraphType,
      x54_no_induced_odd_dicycle D ->
      dicolorableb D (f (ω([set: chi_bounded.underlying D]))).
