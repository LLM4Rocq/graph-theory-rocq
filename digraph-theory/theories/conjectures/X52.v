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

(** Corpus row: arxiv:1610.00876#03
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1610.00876__03/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1610.00876__03.json
    English statement: (Aboulker, Cohen, Havet, Lochet, Moura, Thomasse 2016, arXiv:1610.00876, Conjecture 11)
      For every oriented tree T on k vertices, every finite digraph whose underlying simple
      graph has ordinary chromatic number at least 2k-2 contains a subdivision of T; that is the
      chromatic Mader threshold of T is at most 2k-2.
    Definitions: [x52_mader_chi_bound F m] - every digraph whose underlying graph has chromatic
      number at least m contains a subdivision of F (this file); [contains_subdivision F D]
      (conjectures/X2.v); [oriented_tree T] (conjectures/X2.v); [chi_bounded.underlying]
      (conjectures/chi_bounded.v); [chi] - coq-graph-theory's chromatic number.
    Notes: The chromatic number is the ORDINARY chi of the underlying simple graph, not the
      dichromatic number. The subtraction 2 * k - 2 is natural-number subtraction; for k = 0 or
      1 the hypothesis chromatic number at least 0 holds of every digraph, but no oriented tree
      with fewer than one vertex exists, [oriented_tree] requiring nonemptiness. *)
Definition oriented_tree_mader_chi_linear_bound_statement : Prop :=
  forall (T : orientedDigraph) (k : nat),
    oriented_tree T ->
    #|T| = k ->
    x52_mader_chi_bound T (2 * k - 2).
