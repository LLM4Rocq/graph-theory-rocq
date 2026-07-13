(** * Hypergraph.conjectures.X73 -- v2 regular tripartite matching row *)

From GTBase Require Export base.
From Hypergraph.conjectures Require Import X6.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X73 vocabulary ************************************************)

Definition x73_balanced_tripartite
    (T : finType) (part : T -> 'I_3) (n : nat) : Prop :=
  forall i : 'I_3, #|[set v : T | part v == i]| = n.

Definition x73_hyperdegree (T : finType) (E : {set {set T}}) (v : T) : nat :=
  #|[set e in E | v \in e]|.

Definition x73_regular (T : finType) (E : {set {set T}}) (d : nat) : Prop :=
  forall v : T, x73_hyperdegree E v = d.

(** ** X73 statements ******************************************************)

(** Studies slice: Aharoni-Charbit-Howard conjecture on matchings in
    d-regular n x n x n, 3-partite, 3-uniform hypergraphs.  Edges are a set of
    vertex sets, so repeated edges are excluded by construction. *)
Definition regular_tripartite_hypergraph_matching_lower_bound_statement : Prop :=
  forall (d n : nat) (T : finType) (part : T -> 'I_3) (E : {set {set T}}),
    1 <= d ->
    x73_balanced_tripartite part n ->
    @x6_r_partite_uniform T 3 part E ->
    x73_regular E d ->
    exists M : {set {set T}},
      x6_matching M E /\ ((d.-1 * n) %/ d <= #|M|).
