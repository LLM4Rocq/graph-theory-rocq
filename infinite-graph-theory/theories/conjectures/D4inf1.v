(** * Infinite.conjectures.D4inf1 — unfriendly partitions & unions of triangle-free graphs.

    Two OPEN infinite-combinatorics rows, faithfully stated over the Prop-level
    [iGraph] carrier with NO smuggled choice / cardinal arithmetic / topology.
    "At least as many … as …" and "a union of ℵ₀ …" are rendered by the
    definitional injection ([card_le]) and by a [nat]-indexed edge colouring —
    both first-order [Prop]s.  Vocabulary is in [Infinite.foundations.igraph]. *)

From GTBase Require Export base.
From Infinite Require Import foundations.igraph.
From mathcomp Require Import all_boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** unfriendly_partitions  (Problem, OPEN)

    Source: "A partition of V(G) is unfriendly if every vertex has at least as
    many neighbours in the other classes as in its own.  Does every countably
    infinite graph have an unfriendly partition into two sets?"

    Encoding: a 2-partition is [p : iV G -> bool]; [unfriendly p] asks, at every
    vertex [x], for [card_le (own_nbr p x) (cross_nbr p x)] — i.e. an injection
    from [x]'s same-class neighbours to its other-class neighbours (|own| ≤
    |cross|, the choice-free definition of cardinal ≤).  Guarded by
    [countable_graph]. *)
Definition unfriendly_partitions_statement : Prop :=
  forall G : iGraph, countable_graph G -> exists p : iV G -> bool, unfriendly p.

(** ** unions_of_triangle_free_graphs  (Problem, OPEN)

    Source: "Does there exist a graph with no subgraph isomorphic to K4 which
    cannot be expressed as a union of ℵ₀ triangle-free graphs?"

    Encoding: "union of ℵ₀ triangle-free graphs" is a symmetric [nat] edge
    colouring with no monochromatic triangle ([ctf_cover]); a cover into
    triangle-free subgraphs exists iff such a partition-colouring does.  The row
    asserts the existence of a witness graph [K4_free G /\ ~ ctf_cover G].  Only
    STATED (the truth is the open, ZFC-flavoured problem); nothing is proven. *)
Definition unions_of_triangle_free_graphs_statement : Prop :=
  exists G : iGraph, K4_free G /\ ~ ctf_cover G.
