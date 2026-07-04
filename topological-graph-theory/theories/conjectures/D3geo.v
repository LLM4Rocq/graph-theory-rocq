(** * D3 metric-geometry rows landed via the finite-geometry foundation.

    Track-A metric-geometry preflight outcome: the one row justifying a small
    finite-geometry primitive (the [orient] determinant sign) is
    small_universal_point_sets — a faithful finite/combinatorial encoding over
    an abstract ordered field (points as a [seq], straight-line crossing via
    [orient], planarity via base [wagner_planar]).  The great-circle,
    surface-drawing and obstacle-number rows stay BLOCKED (genuine spherical /
    continuous / arbitrary-closed-set geometry). *)

From GTBase Require Export base.
From mathcomp Require Import all_algebra.
From Topological.foundations Require Import geometry.
Import GRing.Theory Num.Theory.
Set Implicit Arguments.
Unset Strict Implicit.

(** ** Small universal point sets for planar graphs  (OPEN)

    Source (Question): "A set P ⊆ ℝ² is n-universal if every n-vertex planar
    graph can be drawn so each vertex maps to a distinct point in P and all
    edges are non-crossing straight-line segments.  Does there exist an
    n-universal set of size O(n)?"

    Encoding (finite geometry over a real-closed field [R : rcfType],
    [Topological.foundations.geometry]): [n_universal P n] = [P : seq (R*R)] and
    every [wagner_planar] graph on [n] vertices embeds straight-line onto
    distinct points of [P].  "O(n)" = a single constant [c] with, for every [n],
    a universal [P] of size ≤ c·n.  "Non-crossing straight-line" and "distinct
    points" are captured EXACTLY by [straightline_planar]: injective placement,
    NO vertex on a non-incident edge, and INDEPENDENT edges never [seg_meet]
    (share no point — the full closed-segment test, not merely a proper
    crossing).  NO general-position side condition is imposed (the source imposes
    none; grids are universal candidates yet not in general position).

    FAITHFUL TO ℝ² (why [rcfType], not [realFieldType]).  For each fixed [(c,n)]
    the body "[forall G] of order [n], [exists pos] with the sign conditions" is
    a first-order formula in the language of ordered fields (finitely many
    graphs; [orient]-sign atoms).  By Tarski–Seidenberg model-completeness every
    real-closed field satisfies exactly the same first-order sentences, so each
    [(c,n)]-body has field-INDEPENDENT truth across all [rcfType]; the outer
    [exists c ∀n] (arithmetic, outside the field) then also agrees.  Hence
    [forall R : rcfType] is EQUIVALENT to the [R = ℝ] source (ℝ is real-closed) —
    a proof AND a disproof both transfer, unlike a bare [realFieldType]
    quantifier (which would also range over non-real-closed [ℚ] and be a priori
    strictly stronger). *)
Definition small_universal_point_sets_for_planar_graphs_statement : Prop :=
  forall R : rcfType,
    exists c : nat,
      forall n : nat,
        exists P : seq (pt R),
          (size P <= c * n)%N /\ n_universal P n.
