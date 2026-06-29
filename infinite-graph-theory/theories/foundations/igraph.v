(** * Infinite.foundations.igraph — Prop-level carrier for infinite graphs

    [sgraph] (the coq-graph-theory simple-graph type) is built on a [finType]
    of vertices, so it is structurally UNFAITHFUL for infinite graphs.  This
    module provides a thin, Prop-level carrier [iGraph] whose vertex type is an
    arbitrary [Type] and whose edge relation is a [Prop]-valued symmetric,
    irreflexive relation.  All infinite-graph vocabulary lives here (never in
    [base]); milestone D4doa uses it for the K_omega (countable complete graph)
    row.

    Predicates are deliberately PROP-LEVEL: mathcomp's boolean [\in] / [path]
    machinery needs an [eqType]/[finType], which is unavailable for an arbitrary
    vertex type [iV].  Countability, rays, etc. are therefore stated with [exists]
    / first-order [Prop]s and explicit index functions. *)

From mathcomp Require Import all_boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Symmetric / irreflexive Prop-relations and the [iGraph] carrier *)

Definition irel_sym {V} (e : V -> V -> Prop) := forall x y, e x y -> e y x.
Definition irel_irr {V} (e : V -> V -> Prop) := forall x, ~ e x x.

Record iGraph := Build_iGraph {
  iV       : Type;
  iedge    : iV -> iV -> Prop;
  iedge_sym : irel_sym iedge;
  iedge_irr : irel_irr iedge }.

Definition iadj (G : iGraph) (x y : iV G) : Prop := @iedge G x y.

(** A graph is countable when its vertex type injects into [nat]. *)
Definition countable_graph (G : iGraph) : Prop :=
  exists f : iV G -> nat, injective f.

(** A ray is a one-way infinite simple path (the index function is injective and
    consecutive indices are adjacent). *)
Definition ray (G : iGraph) (r : nat -> iV G) : Prop :=
  injective r /\ forall n, iadj (r n) (r n.+1).

(** ** K_omega : the countable complete graph

    Vertices are [nat]; distinct vertices are adjacent.  Every infinite vertex
    subset induces a complete subgraph, so an "infinite complete subgraph" is
    just an injective sequence of vertices (its image is an infinite clique). *)

Lemma Komega_sym : irel_sym (fun x y : nat => x <> y).
Proof. by move=> x y H K; apply: H. Qed.

Lemma Komega_irr : irel_irr (fun x y : nat => x <> y).
Proof. by move=> x H; apply: H. Qed.

Definition Komega : iGraph := Build_iGraph Komega_sym Komega_irr.

Lemma Komega_countable : countable_graph Komega.
Proof. by exists id. Qed.

(** ** Exact edge-colourings of K_omega and exactly-[m]-coloured subgraphs

    An edge colouring of K_omega with [c] colours assigns a colour in ['I_c] to
    every (unordered) pair of distinct vertices; we model it as a symmetric
    function on [nat].  ([col x x] is irrelevant: K_omega has no loops, and the
    predicates below only ever evaluate [col] on distinct arguments.) *)

Definition Kedge_coloring (c : nat) : Type := nat -> nat -> 'I_c.

(** Symmetric on the (only meaningful) distinct pairs — stated unconditionally,
    which is the cleanest faithful rendering of "the colour of edge {x,y}". *)
Definition sym_coloring (c : nat) (col : Kedge_coloring c) : Prop :=
  forall x y, col x y = col y x.

(** Exact [c]-colouring: every one of the [c] colours is used at least once. *)
Definition exact_coloring (c : nat) (col : Kedge_coloring c) : Prop :=
  forall k : 'I_c, exists x y, x <> y /\ col x y = k.

(** A colour [k] is used inside the (complete) subgraph indexed by [s]. *)
Definition uses_color (c : nat) (col : Kedge_coloring c)
    (s : nat -> nat) (k : 'I_c) : Prop :=
  exists i j, i <> j /\ col (s i) (s j) = k.

(** The countably infinite complete subgraph indexed by the injective sequence
    [s] is "exactly [m]-coloured": the (finite) set of colours appearing on its
    edges has cardinality exactly [m]. *)
Definition exactly_m_colored (c : nat) (col : Kedge_coloring c)
    (s : nat -> nat) (m : nat) : Prop :=
  exists T : {set 'I_c}, #|T| = m /\ forall k, (k \in T) <-> uses_color col s k.
