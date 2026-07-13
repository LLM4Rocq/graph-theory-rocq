(** * Digraph.conjectures.X71 -- v2 directed Gyarfas-Sumner row *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude interop_graph_theory digraph oriented.
From Digraph.conjectures Require Import chi_bounded dichromatic heroes.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X71 vocabulary ************************************************)

Definition x71_oriented_forb_ind (F D : diGraphType) : Prop :=
  chi_bounded.oriented_dg D /\ ind_free F D.

(** ** X71 statements ******************************************************)

(** Studies slice: Aboulker-Charbit-Naserasr directed Gyarfas-Sumner conjecture
    (arXiv:1704.07219, 2212.02272): for every oriented forest F, the class
    Forb_ind(F) of oriented graphs with no induced copy of F is chi-vec-BOUNDED.

    [chi-vec-bounded] means the DICHROMATIC number is bounded by a FUNCTION of the
    directed clique number omega-vec(D) = the order of the largest sub-tournament
    of D = omega of the underlying graph (a set of pairwise underlying-adjacent
    vertices is a semicomplete = tournament subdigraph).  We encode this with the
    corpus directed-chi-boundedness idiom [dicolorableb D (f (omega(underlying D)))]
    (identical to X54): exists a single binding function f such that every oriented
    F-free D is f(omega-vec(D))-dicolourable.

    NB. This is a FUNCTION bound, NOT the constant bound [dichromatic_bounded]:
    Forb_ind(F) contains every tournament (a tournament has no induced copy of any
    oriented forest on >= 3 vertices, since a forest has a non-adjacent pair while a
    tournament is semicomplete), and tournaments have UNBOUNDED dichromatic number,
    so no uniform constant bounds the class -- but omega-vec is large on tournaments,
    so the function bound is not violated.  Forbidding a transitive tournament (X123)
    bounds omega-vec, turning this chi-vec-bounded statement into X123's chi-vec-FINITE
    (constant) statement -- so X71 (function bound) is the master form and implies X123. *)
Definition directed_gyarfas_sumner_oriented_forest_dichromatic_statement : Prop :=
  forall F : diGraphType,
    chi_bounded.oriented_dg F ->
    chi_bounded.oriented_forest F ->
    exists f : nat -> nat,
      forall D : diGraphType,
        x71_oriented_forb_ind F D ->
        dicolorableb D (f (ω([set: chi_bounded.underlying D]))).
