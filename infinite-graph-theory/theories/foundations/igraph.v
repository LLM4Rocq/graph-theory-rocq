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

(** ================================================================= *)
(** ** Shared infinite-combinatorics primitives (D4 preflight, M0)

    Carrier-free primitives reused across the D4 rows.  All are first-order
    [Prop]s / inductive definitions — NO choice, NO cardinal arithmetic, NO
    point-set topology.  [card_le] is the injection form of |A| ≤ |B| (its very
    definition, needing no choice); [finite_sub] is an ['I_n]-cover of a
    Prop-subset; [reachP]/[connected_set] are finite-walk reachability INSIDE a
    Prop-subset; [infinite_graph] is Dedekind-infiniteness. *)

(** |{x | P x}| ≤ |{y | Q y}| — the definitional injection form of cardinal ≤. *)
Definition card_le (A B : Type) (P : A -> Prop) (Q : B -> Prop) : Prop :=
  exists f : {x : A | P x} -> {y : B | Q y}, injective f.

(** [P] picks out at most finitely many vertices (an ['I_n]-indexed cover). *)
Definition finite_sub (G : iGraph) (P : iV G -> Prop) : Prop :=
  exists (n : nat) (g : 'I_n -> iV G), forall x, P x -> exists i : 'I_n, g i = x.

(** Reachability from [x] to [y] by an [iedge]-walk all of whose vertices lie in
    [P] (so [reachP P x y -> P x /\ P y]). *)
Inductive reachP (G : iGraph) (P : iV G -> Prop) : iV G -> iV G -> Prop :=
  | reachP0 x : P x -> reachP P x x
  | reachPS x y z : reachP P x y -> iadj y z -> P z -> reachP P x z.

(** [P] induces a connected subgraph. *)
Definition connected_set (G : iGraph) (P : iV G -> Prop) : Prop :=
  forall x y, P x -> P y -> reachP P x y.

(** [G] is (Dedekind-)infinite: [nat] injects into its vertices. *)
Definition infinite_graph (G : iGraph) : Prop :=
  exists f : nat -> iV G, injective f.

(** ** Combinatorial ENDS (Halin) — no point-set topology.

    Two rays are END-EQUIVALENT when no finite vertex set separates their tails:
    for every FINITE [S], late vertices of one ray are joined, in [G − S], to
    late vertices of the other (a walk avoiding [S], via [reachP]).  Since rays
    are injective, each visits any finite [S] only finitely often, so tails do
    eventually avoid [S].  An END is a class of this relation; below it is used
    only through a representative ray. *)
Definition end_equiv (G : iGraph) (r r' : nat -> iV G) : Prop :=
  forall S : iV G -> Prop, finite_sub S ->
    exists N : nat, forall n : nat, N <= n ->
      exists m : nat, N <= m /\ reachP (fun v => ~ S v) (r n) (r' m).

(** ================================================================= *)
(** ** M1 vocabulary — unfriendly partitions & unions of triangle-free graphs *)

(** The same-class / other-class neighbourhoods of [x] under a 2-partition [p]. *)
Definition own_nbr (G : iGraph) (p : iV G -> bool) (x w : iV G) : Prop :=
  iadj x w /\ p w = p x.
Definition cross_nbr (G : iGraph) (p : iV G -> bool) (x w : iV G) : Prop :=
  iadj x w /\ p w <> p x.

(** [p] is UNFRIENDLY: every vertex has at least as many other-class as
    same-class neighbours (|own| ≤ |cross|, via [card_le]). *)
Definition unfriendly (G : iGraph) (p : iV G -> bool) : Prop :=
  forall x : iV G, card_le (own_nbr p x) (cross_nbr p x).

(** [G] contains no [K_4] (four pairwise-adjacent vertices; distinctness is free
    from [iedge_irr]). *)
Definition K4_free (G : iGraph) : Prop :=
  ~ exists a b c d : iV G,
      [/\ iadj a b, iadj a c, iadj a d, iadj b c & iadj b d /\ iadj c d].

(** [G]'s edges are covered by countably many triangle-free graphs: a symmetric
    [nat] edge-colouring with NO monochromatic triangle.  (A cover into
    triangle-free subgraphs exists iff such a partition-colouring does.) *)
Definition ctf_cover (G : iGraph) : Prop :=
  exists col : iV G -> iV G -> nat,
    (forall x y, col x y = col y x) /\
    (forall x y z : iV G, iadj x y -> iadj y z -> iadj x z ->
       col x y = col y z -> col x y = col x z -> False).
