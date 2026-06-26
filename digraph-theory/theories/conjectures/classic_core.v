(** * Digraph.conjectures.classic_core — P9 "classic digraph core"

    The cheapest-to-state, highest-fame open digraph conjectures: they need only a few
    new primitives on top of the existing core (out-degree, directed cycles).
    See docs/CONJECTURES_FORMALIZATION_PLAN.md §4 (P9), §5.

    New primitives (digraph level, mirroring [outdeg]):
      - [Nout v] / [Nin v]      : out- / in-neighbourhood sets
      - [indeg v]               : in-degree (the lib had [N_in] only for tournaments)
      - [Nout2 v]               : second out-neighbourhood (directed distance exactly 2)
      - [diregular d]           : in-degree = out-degree = d at every vertex

    Nodes (Definitions of type Prop):
      - [seymour_second_neighbourhood_statement] : every oriented graph has a vertex v
            with |N⁺⁺(v)| ≥ |N⁺(v)|  (Seymour's Second Neighbourhood Conjecture).
      - [caccetta_haggkvist_statement]           : a loopless digraph with min out-degree
            ≥ r has a directed cycle of length ≤ ⌈n/r⌉  (Caccetta–Häggkvist).
      - [caccetta_haggkvist_triangle_statement]  : an oriented graph with min out-degree
            ≥ n/3 has a directed triangle  (the famous CH triangle case). *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph oriented dipath strong.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** New degree / neighbourhood primitives (general digraph level) *)

Section Degrees.
Variable D : diGraphType.
Implicit Types (v w : D).

Definition Nout v : {set D} := [set w | v --> w].
Definition Nin  v : {set D} := [set u | u --> v].

(** In-degree (companion of [outdeg], which is [#|Nout v|] by definition). *)
Definition indeg v : nat := #|Nin v|.

(** Second out-neighbourhood: vertices at directed distance exactly two from [v]
    (an out-neighbour of an out-neighbour, distinct from [v] and not itself an
    out-neighbour). *)
Definition Nout2 v : {set D} :=
  [set w | [&& w != v, w \notin Nout v & [exists u, (u \in Nout v) && (u --> w)]]].

(** Diregular of degree [d]: every vertex has in-degree and out-degree exactly [d]. *)
Definition diregular (d : nat) : bool := [forall v, (outdeg v == d) && (indeg v == d)].

End Degrees.

(** ** Oriented girth ≥ 3 (reusable)

    An oriented graph has no loops (irreflexive) and no digons (asymmetric), so every
    directed cycle has length at least 3. This is the crux of the eventual
    Caccetta–Häggkvist ⟹ triangle edge (a CH cycle of length ≤ 3 in an oriented graph
    must be exactly a triangle). *)
Lemma oriented_dicycle_size_ge3 (D : orientedDigraph) (c : seq D) :
  dicycle c -> 3 <= size c.
Proof.
move=> /and3P[cn cc cu]; case: c cn cc cu => [|x [|y [|z t]]] //=.
- by move=> _; rewrite andbT arc_irrefl.
- by move=> _ /and3P[axy ayx _]; rewrite (arc_asymm _ _ axy) in ayx.
Qed.

(** ** Seymour's Second Neighbourhood Conjecture *)

(** Every (nonempty) oriented graph has a "Seymour vertex" [v] whose second
    out-neighbourhood is at least as large as its first. *)
Definition seymour_second_neighbourhood_statement : Prop :=
  forall D : orientedDigraph,
    (0 < #|D|)%N -> exists v : D, (outdeg v <= #|Nout2 v|)%N.

(** ** Caccetta–Häggkvist Conjecture *)

(** Every loopless digraph on [n] vertices with minimum out-degree ≥ [r] (≥ 1) has a
    directed cycle of length at most ⌈n/r⌉ = (n + r − 1) %/ r. *)
Definition caccetta_haggkvist_statement : Prop :=
  forall (D : diGraphType) (r : nat),
    (0 < #|D|)%N -> (forall v : D, ~~ (v --> v)) -> (0 < r)%N ->
    (forall v : D, (r <= outdeg v)%N) ->
    exists c : seq D, dicycle c /\ (size c <= (#|D| + r - 1) %/ r)%N.

(** The famous triangle case: an oriented graph whose minimum out-degree is ≥ n/3
    (equivalently n ≤ 3·δ⁺) contains a directed triangle. *)
Definition caccetta_haggkvist_triangle_statement : Prop :=
  forall D : orientedDigraph,
    (0 < #|D|)%N -> (forall v : D, (#|D| <= 3 * outdeg v)%N) ->
    exists c : seq D, dicycle c /\ size c = 3.

(** ** Long directed cycles in diregular digraphs (Bermond–Germa–Heydemann–Sotteau) *)

(** A strongly connected oriented graph with minimum in- and out-degree ≥ d (d ≥ 1) has a
    directed cycle of length at least 2d+1. *)
Definition long_dicycle_diregular_statement : Prop :=
  forall (D : orientedDigraph) (d : nat),
    (0 < #|D|)%N -> (0 < d)%N -> strongb D ->
    (forall v : D, (d <= indeg v)%N) -> (forall v : D, (d <= outdeg v)%N) ->
    exists c : seq D, dicycle c /\ (2 * d + 1 <= size c)%N.

(** ** Hamilton cycle in small diregular oriented graphs (Jackson) *)

(** For d > 2, every d-diregular oriented graph on at most 4d+1 vertices is Hamiltonian
    (has a directed cycle through every vertex). *)
Definition jackson_hamilton_small_diregular_statement : Prop :=
  forall (D : orientedDigraph) (d : nat),
    (0 < #|D|)%N -> 2 < d -> diregular D d -> (#|D| <= 4 * d + 1)%N ->
    exists c : seq D, dicycle c /\ size c = #|D|.

(** ** Splitting a digraph under minimum-out-degree constraints (Alon) *)

(** There is a function f such that every digraph with minimum out-degree ≥ f(d) admits a
    vertex bipartition (V1, V1ᶜ) in which each part induces minimum out-degree ≥ d.
    [outdeg_in A v] is the out-degree of v counting only arcs whose head lies in A — i.e.
    the out-degree of v inside the subdigraph induced by A. *)
Definition splitting_min_outdegree_statement : Prop :=
  exists f : nat -> nat,
    forall (D : diGraphType) (d : nat),
      (forall v : D, (f d <= outdeg v)%N) ->
      exists V1 : {set D},
        [/\ (* a PROPER bipartition: both parts nonempty (without this, V1 := setT makes
               the complement-side constraint vacuous, trivializing the statement) *)
            V1 != set0,
            V1 != [set: D],
            (forall v : D, v \in V1 -> (d <= outdeg_in V1 v)%N)
          & (forall v : D, v \notin V1 -> (d <= outdeg_in (~: V1) v)%N)].

(** ** Stable set meeting all longest directed paths (Laborde–Payan–Xuong) *)

(** A [stable] (independent) set has no arc between any two of its members. *)
Definition stable (D : diGraphType) (S : {set D}) : bool :=
  [forall u in S, [forall v in S, ~~ (u --> v)]].

(** Every digraph has a stable set that meets every longest directed path. *)
Definition stable_meeting_longest_dipaths_statement : Prop :=
  forall D : diGraphType,
    exists S : {set D}, stable S /\
      forall (x : D) (s : seq D), dipath x s -> size s = ell D ->
        exists2 v : D, v \in S & v \in x :: s.
