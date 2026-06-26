(** * Chromatic.conjectures.U8 — milestone U8 (namespace Chromatic, plan v4)

    Statement-only formalizations (axiom-free: no Conjecture/Axiom/Parameter/
    Admitted) of three OPEN problems on the chromatic number and χ-boundedness:

      Row 1  Bounding χ of triangle-free graphs with fixed maximum degree
             (Conjecture: χ(G) ≤ ⌈Δ/2⌉+2 for triangle-free G).
      Row 2  Graphs with a forbidden induced tree are χ-bounded
             (Conjecture: for every fixed tree T, the class of T-induced-free
             graphs is χ-bounded).
      Row 3  Are proper vertex-minor-closed classes χ-bounded?  (Question).

    CARRIER TYPE (all three rows live on SIMPLE undirected graphs):
      - carrier [sgraph]; vertices [x -- y] adjacency.  Row 2 additionally
        ranges over a forbidden tree [T : sgraph]; Row 3 quantifies over a
        graph CLASS [F : sgraph -> Prop].  No multigraph / digraph surface is
        needed, so only the core undirected vocabulary of graph-theory-base is
        imported.

    CORE undirected vocabulary comes from graph-theory-base (GTBase.base), which
    re-exports the coq-graph-theory layer: [sgraph], [x -- y], [χ(A)]=[chi_mem],
    [ω(A)]=[omega_mem], [Delta] (Δ), [ceil_div], [induced] (induced subgraph),
    [is_tree], [F ≃ G]=[diso].  These are REUSED verbatim; no base primitive is
    redefined.

    AREA-SPECIFIC primitives introduced here (χ-boundedness / vertex-minor
    vocabulary, none currently in base — checked via Search over GTBase.base):
      - [chi_bounded] : a class [F : sgraph -> Prop] is χ-bounded — there is a
        bounding function [f : nat -> nat] with [χ(G) ≤ f(ω(G))] for all G ∈ F.
        Shared by Rows 2 and 3 (the common notion both statements assert);
        a Coloring-area primitive [@MOVE-to-base candidate when a 2nd area
        outside Chromatic needs it].
      - [has_induced] : G contains an induced subgraph isomorphic to T
        (induced-subgraph-iso), the forbidden-subgraph relation of Row 2.
      - [local_complement] / [vminorR] / [vertex_minor] : local complementation
        at a vertex, the reflexive vertex-minor reachability relation (closure
        under local complementation and vertex deletion, up to isomorphism), and
        the vertex-minor relation of Row 3.
      - [vminor_closed] / [proper_class] : a class closed under taking
        vertex-minors / a proper class (some graph omitted), Row 3's hypotheses.

    is-tree is REUSED from base ([is_tree], = is_forest ∧ connected). *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ============================================================================
    SHARED AREA PRIMITIVE — χ-boundedness (Rows 2 and 3).
    "A family F is χ-bounded if there is f : ℕ → ℕ with χ(G) ≤ f(ω(G)) for every
    G ∈ F."  A class is modelled as a predicate [F : sgraph -> Prop]; the bound
    is the whole-graph [χ([set: G])] against [ω([set: G])].
    ========================================================================== *)

Definition chi_bounded (F : sgraph -> Prop) : Prop :=
  exists f : nat -> nat,
    forall G : sgraph, F G -> χ([set: G]) <= f (ω([set: G])).

(** ============================================================================
    Row 1 — Bounding the chromatic number of triangle-free graphs with fixed
    maximum degree — OPEN.
    "Conjecture: a triangle-free graph with maximum degree Δ has chromatic
    number at most ⌈Δ/2⌉+2."  Triangle-freeness is stated directly: no three
    mutually adjacent vertices (their pairwise distinctness is automatic from
    irreflexivity of [--]).  ⌈Δ/2⌉ = [ceil_div (Delta G) 2].
    ========================================================================== *)

Definition bounding_the_chromatic_number_of_triangle_free_graph_statement : Prop :=
  forall G : sgraph,
    (forall x y z : G, x -- y -> y -- z -> z -- x -> False) ->
    χ([set: G]) <= ceil_div (Delta G) 2 + 2.

(** ============================================================================
    Row 2 — Graphs with a forbidden induced tree are χ-bounded — OPEN.
    "For every fixed tree T, the family of graphs with no induced subgraph
    isomorphic to T is χ-bounded."  [has_induced T G] : G has an induced
    subgraph ([induced S] on some vertex set S) isomorphic to T; the family is
    the complement predicate [fun G => ~ has_induced T G].  The tree hypothesis
    on T is base's [is_tree [set: T]] (forest + connected over all of T).
    ========================================================================== *)

(** induced-subgraph-iso: T occurs as an induced subgraph of G.  [≃] = [diso]
    lands in Type, so it is wrapped in [inhabited] to land in Prop. *)
Definition has_induced (T G : sgraph) : Prop :=
  exists S : {set G}, inhabited (T ≃ induced S).

Definition graphs_with_a_forbidden_induced_tree_are_chi_bounded_statement : Prop :=
  forall T : sgraph, is_tree [set: T] ->
    chi_bounded (fun G : sgraph => ~ has_induced T G).

(** ============================================================================
    Row 3 — Are proper vertex-minor-closed classes χ-bounded? — OPEN QUESTION.
    "Is every proper vertex-minor closed class of graphs χ-bounded?"  Stated as
    the affirmative proposition.  A vertex-minor is obtained from G by a finite
    sequence of LOCAL COMPLEMENTATIONS and VERTEX DELETIONS (up to isomorphism).
    Local complementation at v complements the edges among the neighbours of v.
    ========================================================================== *)

(** Local complementation at [v]: toggle adjacency between every pair of
    DISTINCT vertices both adjacent to [v]; all other pairs (and edges incident
    to v) are unchanged.  Built as a genuine [sgraph]: the [x != y] guard makes
    it irreflexive, and each conjunct is symmetric, so the relation is. *)
Section LocalComplement.
Variables (G : sgraph) (v : G).
Definition lc_rel : rel G :=
  fun x y => (x != y) && ((x -- y) (+) ((x -- v) && (y -- v))).
Lemma lc_sym : symmetric lc_rel.
Proof.
move=> x y; rewrite /lc_rel eq_sym sgP [(x -- v) && _]andbC.
by [].
Qed.
Lemma lc_irrefl : irreflexive lc_rel.
Proof. by move=> x; rewrite /lc_rel eqxx. Qed.
Definition local_complement : sgraph := SGraph lc_sym lc_irrefl.
End LocalComplement.

(** [vminorR G H] : H is reachable from G by local complementations and vertex
    deletions, up to simple-graph isomorphism ([≃]).  Vertex deletion of [v] is
    the induced subgraph on [[set u | u != v]]. *)
Inductive vminorR : sgraph -> sgraph -> Prop :=
| vminorR_refl (G : sgraph) : vminorR G G
| vminorR_lc (G H K : sgraph) (v : H) :
    vminorR G H -> (local_complement v ≃ K) -> vminorR G K
| vminorR_del (G H K : sgraph) (v : H) :
    vminorR G H -> (induced [set u : H | u != v] ≃ K) -> vminorR G K.

(** H is a vertex-minor of G. *)
Definition vertex_minor (H G : sgraph) : Prop := vminorR G H.

(** A class closed under taking vertex-minors. *)
Definition vminor_closed (F : sgraph -> Prop) : Prop :=
  forall G H : sgraph, F G -> vertex_minor H G -> F H.

(** A proper class: it omits some graph (it is not the class of ALL graphs).
    This is the non-triviality guard pinning the question to PROPER classes —
    the class of all graphs is vertex-minor-closed but not χ-bounded. *)
Definition proper_class (F : sgraph -> Prop) : Prop :=
  exists G : sgraph, ~ F G.

Definition vertex_minor_closed_classes_are_chi_bounded_statement : Prop :=
  forall F : sgraph -> Prop,
    vminor_closed F -> proper_class F -> chi_bounded F.
