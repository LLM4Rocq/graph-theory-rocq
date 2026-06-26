(** * Cycle.conjectures.U10 — milestone U10 (namespace Cycle, plan v4)

    Statement-only formalizations (axiom-free: no Conjecture/Axiom/Parameter/
    Admitted) of three central OPEN conjectures on perfect matchings of
    bridgeless cubic graphs:

      - Row 1 : the Berge–Fulkerson Conjecture
                (six perfect matchings double-covering the edges);
      - Row 2 : the Petersen Colouring Conjecture
                (an edge-colouring by the edges of the Petersen graph respecting
                 mutual adjacency of edge-triples);
      - Row 3 : the Fan–Raspaud "intersecting two perfect matchings" Conjecture
                (two perfect matchings whose intersection contains no odd
                 edge-cut).

    CARRIER.  The host graph [G] of each row is an undirected MULTIGRAPH, so its
    carrier is coq-graph-theory's [mgraph] = [graph unit unit] — exactly the
    object level of the sibling milestone [U6.v], whose cycle-theory vocabulary
    ([cubic], [bridgeless], [subdeg], [cut], [is_matching]) we REUSE verbatim by
    importing [U6].  Matchings are EDGE SETS [{set edge G}]; a perfect-matching
    cover / a list of matchings is a [seq {set edge G}].

    For Row 2 the codomain is THE Petersen graph, which we build concretely as
    the Kneser graph KG(5,2): vertices are the 2-element subsets of ['I_5],
    adjacency is disjointness ([petersen : sgraph]).  Its "edges" are the
    adjacent vertex pairs ([Pedge]); edge-adjacency in [G] reuses base's
    undirected [line_graph]/[line_rel] (mgraph edges sharing an endpoint).

    IMPORT ORDER: [mgraph] (and [sgraph]) are imported BEFORE [base], because
    coq-graph-theory's [mgraph] ships a DIRECTED [line_graph] that would
    otherwise shadow base's undirected one (which [U6] and this file use).

    CORE API used (verified on switch `digraph`, Rocq 9.1.1 + coq-graph-theory):
      - [edge G] : finType of edges; [source e]/[target e] : endpoints;
      - [subdeg H v] (U6) : degree of [v] inside edge set [H];
      - [cut S] (U6) : the edge cut of a vertex set [S];
      - [cubic]/[bridgeless] (U6) : loopless 3-regular / no bridge;
      - [SGraph] : sgraph constructor; [sedge]/[--] : adjacency;
      - base's [line_graph G : sgraph] with [sedge = line_rel] (edges of [G]
        sharing an endpoint).

    AREA primitives introduced here (cycle-theory specific):
      [is_perfect_matching], [perfect_matching_cover] (Row 1);
      [petersenV], [padj], [petersen], [Pedge], [psupp], [Padj], [mut_adj3],
      [cubic_bridgeless] (Row 2);
      [is_odd_edge_cut], [contains_odd_edge_cut] (Row 3). *)

From GraphTheory Require Import mgraph sgraph.
From GTBase Require Import base.
From Cycle.conjectures Require Import U6.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Shared primitives *)

(** A PERFECT matching: every vertex meets EXACTLY one matching edge (sharpening
    U6's [is_matching], which only bounds the matching-degree by one). *)
Definition is_perfect_matching (G : mgraph) (M : {set edge G}) : Prop :=
  forall v : G, subdeg M v = 1.

(** Cubic and bridgeless together: the shared "bridgeless cubic graph" hypothesis
    used uniformly by all three rows. *)
Definition cubic_bridgeless (G : mgraph) : Prop := cubic G /\ bridgeless G.

(** ================================================================= *)
(** ** Row 1 — The Berge–Fulkerson Conjecture *)
(** OPEN.

    Source: "If G is a bridgeless cubic graph, then there exist 6 perfect
    matchings M_1,...,M_6 of G with the property that every edge of G is
    contained in exactly two of M_1,...,M_6." *)

(** A [k]-perfect-matching cover: a list of [k] perfect matchings covering every
    edge exactly twice (a "perfect-matching double cover" of [k] members). *)
Definition perfect_matching_cover (G : mgraph) (k : nat)
    (L : seq {set edge G}) : Prop :=
  [/\ size L = k,
      (forall M, M \in L -> is_perfect_matching M)
    & forall e : edge G, count (fun M : {set edge G} => e \in M) L = 2].

Definition the_berge_fulkerson_statement : Prop :=
  forall G : mgraph,
    (0 < #|G|)%N -> cubic_bridgeless G ->
    exists L : seq {set edge G}, perfect_matching_cover 6 L.

(** ================================================================= *)
(** ** Row 2 — The Petersen Colouring Conjecture *)
(** OPEN.

    Source: "Let G be a cubic graph with no bridge.  Then there is a colouring of
    the edges of G using the edges of the Petersen graph so that any three
    mutually adjacent edges of G map to three mutually adjacent edges in the
    Petersen graph." *)

(** *** THE Petersen graph as the Kneser graph KG(5,2). *)

(** Vertices: the 2-element subsets of a 5-element set (exactly 10 of them). *)
Definition petersenV : finType := {x : {set 'I_5} | #|x| == 2}.

(** Adjacency: two 2-subsets are adjacent iff they are DISJOINT. *)
Definition padj (x y : petersenV) : bool := [disjoint val x & val y].

Lemma padj_sym : symmetric padj.
Proof. by move=> x y; rewrite /padj disjoint_sym. Qed.

Lemma padj_irrefl : irreflexive padj.
Proof.
move=> x; apply/negP; rewrite /padj -setI_eq0 setIid => /eqP Hx.
by move: (valP x); rewrite Hx cards0.
Qed.

Definition petersen : sgraph := SGraph padj_sym padj_irrefl.

(** *** Edges of the Petersen graph, and edge-adjacency. *)

(** A Petersen edge is an adjacent (ordered representative of an) vertex pair. *)
Definition Pedge : finType := {p : petersenV * petersenV | padj p.1 p.2}.

(** The unordered support (endpoint set) of a Petersen edge. *)
Definition psupp (q : Pedge) : {set petersenV} := [set (val q).1; (val q).2].

(** Two Petersen edges are ADJACENT iff they are distinct edges (distinct
    supports) sharing a vertex.  Using supports makes this independent of the
    chosen orientation of each representative. *)
Definition Padj (q r : Pedge) : bool :=
  (psupp q != psupp r) && (psupp q :&: psupp r != set0).

(** Three elements are pairwise related by [r] ("mutually adjacent").
    [@MOVE-to-base]: a carrier-agnostic mutual-adjacency-triple combinator over an
    arbitrary [rel T]; kept area-local for now (base exposes no equivalent —
    confirmed via Search over GTBase.base), migrate to graph-theory-base when a
    second area needs a mutual-adjacency triple. *)
Definition mut_adj3 (T : Type) (r : rel T) (a b c : T) : bool :=
  [&& r a b, r b c & r a c].

(** A Petersen colouring: a map from the edges of [G] to the edges of the
    Petersen graph sending every mutually-adjacent triple of [G]-edges (edges
    pairwise sharing an endpoint, i.e. adjacent in [line_graph G]) to a
    mutually-adjacent triple of Petersen edges. *)
Definition petersen_coloring_statement : Prop :=
  forall G : mgraph,
    (0 < #|G|)%N -> cubic_bridgeless G ->
    exists f : edge G -> Pedge,
      forall e1 e2 e3 : edge G,
        mut_adj3 (@line_rel G) e1 e2 e3 ->
        mut_adj3 Padj (f e1) (f e2) (f e3).

(** ================================================================= *)
(** ** Row 3 — Intersecting two perfect matchings (Fan–Raspaud) *)
(** OPEN.

    Source: "Every bridgeless cubic graph has two perfect matchings M_1, M_2 so
    that M_1 ∩ M_2 does not contain an odd edge-cut." *)

(** An ODD edge-cut: a (nonempty) edge cut [cut S] of odd cardinality.  (The
    [T != set0] clause is kept for readability even though [odd #|set0| = false]
    already forces nonemptiness — see [grounding_U10.is_odd_edge_cut_neq0].) *)
Definition is_odd_edge_cut (G : mgraph) (T : {set edge G}) : Prop :=
  exists S : {set G}, [/\ T = cut S, T != set0 & odd #|T|].

(** An edge set CONTAINS an odd edge-cut iff some odd edge-cut is a subset. *)
Definition contains_odd_edge_cut (G : mgraph) (H : {set edge G}) : Prop :=
  exists T : {set edge G}, T \subset H /\ is_odd_edge_cut T.

(** NOTE: following the source ("two perfect matchings M1, M2") no distinctness
    [M1 != M2] is imposed; coincident matchings are deliberately permitted (the
    single-matching case is still non-trivial). *)
Definition intersecting_two_perfect_matchings_statement : Prop :=
  forall G : mgraph,
    (0 < #|G|)%N -> cubic_bridgeless G ->
    exists M1 M2 : {set edge G},
      [/\ is_perfect_matching M1, is_perfect_matching M2
        & ~ contains_odd_edge_cut (M1 :&: M2)].
