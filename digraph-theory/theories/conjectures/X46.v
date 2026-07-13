(** * Digraph.conjectures.X46 -- v2 bipartite Caccetta-Haggkvist row *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph oriented dipath.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X46 vocabulary ************************************************)

Definition x46_bipartition
    (D : diGraphType) (A B : {set D}) (n : nat) : Prop :=
  [disjoint A & B] /\
  A :|: B = [set: D] /\
  #|A| = n /\
  #|B| = n /\
  forall u v : D,
    u --> v ->
    ((u \in A) && (v \in B)) || ((u \in B) && (v \in A)).

(** ** X46 statements ******************************************************)

(** arXiv:1809.08324, bipartite Caccetta-Haggkvist type bound. *)
Definition bipartite_digraph_outdegree_girth_statement : Prop :=
  forall (k n : nat) (D : diGraphType) (A B : {set D}),
    1 <= k ->
    0 < n ->
    x46_bipartition A B n ->
    (forall v : D, n < k.+1 * outdeg v) ->
    exists c : seq D,
      dicycle c /\
      size c <= 2 * k.
