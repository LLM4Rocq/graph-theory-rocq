(** * Digraph.conjectures.heroes_dichotomy — P6 (cont.): the hero-dichotomy conjectures

    The dichotomy / value statements of the heroes corpus (Aboulker–Charbit–Naserasr,
    arXiv:2009.13319), built on the [Forb_ind] / [heroic] / [hero] machinery of heroes.v
    and the dichromatic keystone. Adds the structural predicates these conjectures need:
    the underlying (undirected) graph and its [oriented_forest] / star-forest notions
    (via graph-theory's [is_forest]), transitive tournaments, and the small forbidden
    patterns (stated in the self-contained "no induced pattern" first-order form, which
    avoids fresh finite-type boilerplate).

    Statements:
      - [conj_6_2]  : χ⃗(Forb_ind(digon, C₃, S₂⁺)) ≤ 2  — the smallest OPEN beachhead.
      - [thm_6_1]   : χ⃗(Forb_ind(digon, C₃, →K₂+K₁)) ≤ 2 — proved landmark (as a target).
      - [conj_4_4]  : {digon, K_l, F} is heroic for every oriented forest F and every l.
      - [conj_4_2]  : the hero dichotomy — {digon, H, F} heroic iff F is a star forest or
                      H is a transitive tournament.
    See docs/CONJECTURES_FORMALIZATION_PLAN.md §4 (P6). *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude interop_graph_theory digraph oriented tournament.
From Digraph Require Import dichromatic heroes.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** The underlying (undirected) graph and forest / star-forest predicates *)

Section Underlying.
Variable F : orientedDigraph.
Definition urel : rel F := fun u v => (u --> v) || (v --> u).
Fact urel_sym : symmetric urel. Proof. by move=> u v; rewrite /urel orbC. Qed.
Fact urel_irrefl : irreflexive urel. Proof. by move=> u; rewrite /urel arc_irrefl. Qed.
(** The underlying simple graph of an oriented graph (forget arc directions). *)
Definition underlying : sgraph := SGraph urel_sym urel_irrefl.
End Underlying.

(** [F] is an oriented forest: its underlying graph is acyclic. *)
Definition oriented_forest (F : orientedDigraph) : Prop :=
  is_forest [set: underlying F].

(** [F] is a disjoint union of oriented stars = an oriented forest with no path on four
    vertices (a tree with no P₄ is a star). *)
Definition no_P4 (F : orientedDigraph) : Prop :=
  ~ exists a b c d : F,
      [/\ uniq [:: a; b; c; d], urel a b, urel b c & urel c d].
Definition union_of_oriented_stars (F : orientedDigraph) : Prop :=
  oriented_forest F /\ no_P4 F.

(** A transitive tournament: a tournament whose arc relation is transitive. *)
Definition transitive_tournament (H : diGraphType) : Prop :=
  is_tournament H /\ transitive (@arc H).

(** ** Forbidden small patterns (self-contained "no induced pattern" form) *)

(** Digon-free = oriented (asymmetric; this also forbids loops). *)
Definition oriented_dg (D : diGraphType) : Prop :=
  forall u v : D, u --> v -> ~~ (v --> u).

(** No induced directed triangle C₃. *)
Definition no_induced_C3 (D : diGraphType) : Prop :=
  ~ exists a b c : D, [/\ a --> b, b --> c & c --> a].

(** No induced out-star S₂⁺ (centre x with x→a, x→b and {a,b} otherwise non-adjacent). *)
Definition no_induced_S2plus (D : diGraphType) : Prop :=
  ~ exists x a b : D,
      x != a /\ x != b /\ a != b /\ x --> a /\ x --> b /\
      ~~ (a --> b) /\ ~~ (b --> a) /\ ~~ (a --> x) /\ ~~ (b --> x).

(** No induced →K₂+K₁ (an arc a→b together with a vertex c isolated from {a,b}). *)
Definition no_induced_arrowK2_K1 (D : diGraphType) : Prop :=
  ~ exists a b c : D,
      a != b /\ a != c /\ b != c /\ a --> b /\ ~~ (b --> a) /\
      ~~ (a --> c) /\ ~~ (c --> a) /\ ~~ (b --> c) /\ ~~ (c --> b).

(** No induced orientation of K_l (no l pairwise-adjacent vertices). *)
Definition no_induced_Kl (l : nat) (D : diGraphType) : Prop :=
  ~ exists S : {set D},
      #|S| = l /\
      (forall u v : D, u \in S -> v \in S -> u != v -> (u --> v) || (v --> u)).

(** ** The conjectures *)

(** Conjecture 6.2 (smallest OPEN beachhead): every oriented, C₃-free, S₂⁺-free digraph
    is 2-dicolourable. (Value-2: ≤ 2 is the open content; the directed C₄ attains 2.) *)
Definition conj_6_2 : Prop :=
  forall D : diGraphType,
    oriented_dg D -> no_induced_C3 D -> no_induced_S2plus D -> dicolorableb D 2.

(** Theorem 6.1 (proved landmark, as a target): every oriented, C₃-free, →K₂+K₁-free
    digraph is 2-dicolourable. *)
Definition thm_6_1 : Prop :=
  forall D : diGraphType,
    oriented_dg D -> no_induced_C3 D -> no_induced_arrowK2_K1 D -> dicolorableb D 2.

(** Conjecture 4.4: for every oriented forest F and every l, the set {digon, K_l, F} is
    heroic — i.e. oriented K_l-free F-free digraphs have bounded dichromatic number. *)
Definition conj_4_4 : Prop :=
  forall (F : orientedDigraph) (l : nat),
    oriented_forest F ->
    dichromatic_bounded
      (fun D : diGraphType => [/\ oriented_dg D, no_induced_Kl l D & ind_free F D]).

(** Conjecture 4.2 (the hero dichotomy): for a hero H and an oriented forest F, the set
    {digon, H, F} is heroic iff F is a disjoint union of oriented stars or H is a
    transitive tournament. *)
Definition conj_4_2 : Prop :=
  forall (H F : orientedDigraph),
    hero H -> oriented_forest F ->
    ( dichromatic_bounded
        (fun D : diGraphType => [/\ oriented_dg D, ind_free H D & ind_free F D])
      <-> (union_of_oriented_stars F \/ transitive_tournament H) ).
