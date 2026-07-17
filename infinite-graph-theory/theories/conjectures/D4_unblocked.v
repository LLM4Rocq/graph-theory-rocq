(** * Infinite.conjectures.D4_unblocked -- legacy blocked OPG rows *)

From mathcomp Require Import all_boot.
From Infinite Require Import foundations.igraph.
From Infinite.conjectures Require Import D4inf4.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition i_neighbourhood (G : iGraph) (x : iV G) (y : iV G) : Prop :=
  iadj x y.

Definition countably_infinite_neighbourhood (G : iGraph) (x : iV G) : Prop :=
  exists f : nat -> {y : iV G | i_neighbourhood x y},
    injective f /\
    forall y : {y : iV G | i_neighbourhood x y}, exists n : nat, f n = y.

Definition uncountable_neighbourhood (G : iGraph) (x : iV G) : Prop :=
  ~ exists f : {y : iV G | i_neighbourhood x y} -> nat, injective f.

Definition aleph0_aleph1_bipartition (G : iGraph) (A B : iV G -> Prop) : Prop :=
  (forall x : iV G, A x \/ B x) /\
  (forall x : iV G, ~(A x /\ B x)) /\
  (forall x y : iV G, iadj x y -> (A x /\ B y) \/ (B x /\ A y)) /\
  (forall x : iV G, A x -> countably_infinite_neighbourhood x) /\
  (forall x : iV G, B x -> uncountable_neighbourhood x).

Definition aleph0_aleph1_graph (G : iGraph) : Prop :=
  exists A B : iV G -> Prop, aleph0_aleph1_bipartition A B.

Definition characterizing_aleph_0_aleph_1_graphs_statement : Prop :=
  exists Characterized : iGraph -> Prop,
    forall G : iGraph, Characterized G <-> aleph0_aleph1_graph G.

Definition d_two_ended (G : iDigraph) : Prop :=
  exists r1 r2 : nat -> dV G,
    injective r1 /\ injective r2 /\
    (forall n : nat, darc (r1 n) (r1 n.+1)) /\
    (forall n : nat, darc (r2 n.+1) (r2 n)).

Definition d_tile (G : iDigraph) (A B : dV G -> Prop) : Prop :=
  (exists a : dV G, A a) /\ (exists b : dV G, B b) /\
  forall x y : dV G, A x -> B y -> darc x y \/ darc y x \/ (~ darc x y /\ ~ darc y x).

Definition d_tile_complete_bipartite_union (G : iDigraph) (A B : dV G -> Prop) : Prop :=
  d_tile A B /\
  forall x y : dV G, A x -> B y -> darc x y \/ darc y x.

Definition highly_arc_transitive_two_ended_digraphs_statement : Prop :=
  forall G : iDigraph,
    highly_arc_transitive G ->
    d_locally_finite G ->
    d_two_ended G ->
    forall A B : dV G -> Prop,
      d_tile A B -> d_tile_complete_bipartite_union A B.

