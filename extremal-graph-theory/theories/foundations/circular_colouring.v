(** * Extremal.foundations.circular_colouring — shared circular-colouring vocabulary

    The carrier-agnostic CIRCULAR-COLOURING layer of milestone D2chr (namespace
    Extremal, plan v4), factored out of the conjecture file because it is used by
    several rows: the mixing-threshold row (M_c), the triangle-free planar
    circular-chromatic row, and the orthogonality-graph row all need the circular
    chromatic number, and the circular-choosability row needs the (p,q)-colouring
    predicate it is built on.

    Everything here is parametric in an ABSTRACT vertex type [V] with a boolean
    adjacency [adj : V -> V -> bool] (NOT [sgraph]); this is deliberate, so the SAME
    [is_circular_chromatic] applies both to a finite [sgraph] (instantiate
    [adj := fun x y => x -- y]) and to the INFINITE orthogonality graph on lines of
    [R^3] (instantiate [adj := perpendicularity]).  No finiteness is assumed.

    The [(p,q)]-colouring follows the source text verbatim — a colouring
    [c : V -> nat] with [c v < p] and, on every edge [uv], [q <= |c u - c v| <= p - q]
    (the LINEAR difference of the source, not the cyclic metric).  [|.|] is the
    integer absolute value [absz] of the [int] difference of the (nat-)colours.

    IMPORT ORDER: only the undirected base surface is needed (no multigraph API),
    so [base] is imported directly; [all_algebra] supplies [int]/[absz]/[rat]. *)

From GTBase Require Export base.
From mathcomp Require Import all_algebra.
Import GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

(** A [(p,q)]-colouring of [(V, adj)]: colours in [{0,…,p-1}] with every edge's
    endpoints at linear colour-distance in [[q, p-q]]. *)
Definition pq_colouring (V : Type) (adj : V -> V -> bool) (p q : nat) (c : V -> nat) : Prop :=
  (forall v, (c v < p)%N) /\
  (forall u v, adj u v ->
     (q <= absz (Posz (c u) - Posz (c v)))%N /\
     (absz (Posz (c u) - Posz (c v)) <= p - q)%N).

(** The circular chromatic number χ_c as a RELATION: [r] is the infimum of the
    ratios [p/q] over all [(p,q)]-colourings, AND that infimum is attained.  Stated
    relationally (achieved lower bound) to stay proof-free; for finite graphs χ_c is
    a well-defined attained rational, so this pins the value. *)
Definition is_circular_chromatic (V : Type) (adj : V -> V -> bool) (r : rat) : Prop :=
  (exists p q : nat, (0 < q)%N /\ (exists c, pq_colouring adj p q c) /\ r = p%:Q / q%:Q) /\
  (forall p q : nat, (0 < q)%N -> (exists c, pq_colouring adj p q c) -> r <= p%:Q / q%:Q).
