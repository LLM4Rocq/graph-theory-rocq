(** * Extremal.conjectures.D2tur — milestone D2tur open-problem statements (Extremal)

    Statement-only formalisation (plan v4, namespace [Extremal]) of six deferred open
    problems / conjectures in extremal & structural graph theory.  Each node is a single
    [Definition <formal_name> : Prop]; the carrier type is chosen PER ROW from the row's
    [rocq_idiom] (NOT a blanket [forall G : sgraph]).  No axioms, no [Admitted], no
    [Conjecture]/[Parameter].

    Sources (verbatim, from the OPG corpus):

    - what_is_the_smallest_number_of_disjoint_spanning_tre_statement (Question, OPEN):
        greedy disjoint shortest-spanning-tree decomposition T_1,T_2,... of a complete
        weighted graph; smallest k whose union T^k contains a Hamiltonian path.  Q1 is
        formalised faithfully; Q2 (SHORTEST Hamiltonian path), Q3/Q4 (1-trees, Hamiltonian
        cycle) are NOT formalised — see the PARTIAL note at that row.

    - turan_number_of_a_finite_family_statement (Conjecture, OPEN):
        "For every finite family F of graphs there exists an F0 in F such that
         ex(n,F0) = O(ex(n,F))."

    - good_edge_labelings_statement (Conjecture, OPEN):
        "For every c<4, there is only a finite number of good-edge-labeling critical
         graphs with average degree less than c."  (The companion Question — max edge
         density of a good-edge-labelable graph — is the supremum of [oedges/2 / #|G|]
         over such graphs; the Conjecture is the precise primary statement.)

    - sidorenkos_statement (Conjecture, OPEN):
        "For any bipartite graph H and graph G, the number of homomorphisms from H to G
         is at least (2|E(G)|/|V(G)|^2)^|E(H)| |V(G)|^|V(H)|."

    - number_of_cliques_in_minor_closed_classes_statement (Question, OPEN):
        "Is there a constant c such that every n-vertex K_t-minor-free graph has at most
         c^t n cliques?"

    - minimal_graphs_with_a_prescribed_number_of_spanning_statement (Conjecture, OPEN):
        "Let n>=3 and let alpha(n) be the least k such that some simple graph on k
         vertices has precisely n spanning trees.  Then alpha(n) = o(log n)."

    Cross-area primitives are REUSED verbatim from [GTBase.base] / coq-graph-theory:
    [N(x)] degree and [average_degree_geq] (Row 3 average-degree side condition, base),
    [is_hom] (the homomorphism predicate reflected inside [hom_count], Row 4, base),
    [oedge] (the ordered-edge selector underlying [edge_count], base), [minor] and
    ['K_t] (Row 5), [cliqueb] (Row 5), and [subgraph] (Rows 2/3, coq-graph-theory).
    Tree/spanning connectivity uses mathcomp's [connect] on the chosen edge relation (no
    [connected] primitive is taken from base).  Genuinely NEW cross-area primitives are
    defined locally and tagged [@MOVE-to-base] (they migrate to base on a 2nd consumer):
    [oedges], [edge_count], [bipartite], [hom_count], [clique_count].

    ASYMPTOTIC ROWS use the eventual-bound / cross-multiplied integer formulation over
    [nat] (never an informal o/O token):
      - "ex(n,F0) = O(ex(n,F))"  ↦  ∃ C N, ∀ n>=N, ex(n,F0) <= C * ex(n,F);
      - "alpha(n) = o(log_2 n)"  ↦  ∀ a b>0, ∃ N, ∀ n>=N, 2^(b*alpha(n)) < n^a
        (using a < (a/b)*log2 n  ⇔  2^(b*a) < n^a — log-free, base-independent). *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import digraph sgraph minor.
From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Shared sgraph counting primitives

    [oedges G] = number of ORDERED adjacent pairs = 2|E(G)| (adjacency is symmetric and
    irreflexive, so this is exactly twice the undirected edge count).  [edge_count G] =
    |E(G)|, defined by REUSING base's [oedge] selector (the ordered pair (x,y) with
    [x -- y] and [enum_rank x < enum_rank y]), so it counts each undirected edge once and
    avoids the [%/ 2] round-trip; [oedges G = 2 * edge_count G] (see grounding).  Used by
    the Turán-number and Sidorenko rows.  Both are new cross-area primitives. *)
(** [@MOVE-to-base] *)
Definition oedges (G : sgraph) : nat := #|[set p : G * G | p.1 -- p.2]|.
(** [@MOVE-to-base] *)
Definition edge_count (G : sgraph) : nat := #|[set p : G * G | oedge p]|.

(** ============================================================================ *)
(** ** Row 1 — Smallest number of disjoint shortest spanning trees → Hamiltonian path

    CARRIER: a complete simple undirected weighted graph = a finite vertex type [V]
    with a symmetric weight [w : V -> V -> nat] (the complete graph K_V carries a weight
    on every pair).  Edge sets are [{set V * V}] (symmetric, irreflexive, sub-relations
    of "distinct pair").

    AREA-SPECIFIC primitives (structural, NOT a cost model):
    - [all_pairs V]      : the edge set of the complete graph K_V (all distinct pairs);
    - [tree_on A E]      : [E] is a SPANNING TREE drawn from the available edge set [A]
                           (E ⊆ A, symmetric, irreflexive, spanning-connected, and with
                           exactly |V|-1 edges — connected + (n-1) edges ⇔ tree);
    - [tree_weight w E]  : total weight of an edge set;
    - [shortest_tree_on] : a minimum-weight spanning tree of the available graph;
    - [greedy_decomp w D k]: D 0,…,D (k-1) is a greedy disjoint decomposition — each
                           [D i] is a shortest spanning tree of K_V with the previously
                           chosen trees' edges removed ("arbitrary shortest spanning tree"
                           is the ∃-witness in the statement);
    - [ham_path_edges E] : the edge set [E] contains a Hamiltonian path (a vertex order
                           visiting every vertex once, consecutive vertices joined in E).

    Q1 (primary): the question is well-posed — for every complete weighted graph on ≥2
    vertices there EXISTS a greedy disjoint shortest-spanning-tree decomposition and a
    SMALLEST [k] such that the union of the first [k] trees contains a Hamiltonian path.

    PARTIAL — Q2 (the union contains a SHORTEST Hamiltonian path), Q3 and Q4 (replacing
    spanning trees by 1-trees; Hamiltonian CYCLE) are NOT formalised here: "shortest
    Hamiltonian path/cycle" needs an optimisation over all Hamiltonian paths/cycles and
    the "1-tree" primitive (a spanning tree on V∖{v} plus two edges at v) — both deferred
    to an applications module. *)

Section WeightedSpanningTrees.
Variable V : finType.

Definition all_pairs : {set V * V} := [set p : V * V | p.1 != p.2].

Definition tree_on (A E : {set V * V}) : bool :=
  [&& (E \subset A),
      [forall p : V * V, (p \in E) == ((p.2, p.1) \in E)],
      [forall x : V, (x, x) \notin E],
      [forall x : V, [forall y : V, connect (fun a b => (a, b) \in E) x y]]
    & #|E| == 2 * (#|V|).-1 ].

Definition tree_weight (w : V -> V -> nat) (E : {set V * V}) : nat :=
  \sum_(p in E) w p.1 p.2.

Definition shortest_tree_on (w : V -> V -> nat) (A E : {set V * V}) : Prop :=
  tree_on A E /\ forall E' : {set V * V}, tree_on A E' -> tree_weight w E <= tree_weight w E'.

Definition greedy_decomp (w : V -> V -> nat) (D : nat -> {set V * V}) (k : nat) : Prop :=
  forall i : nat, (i < k)%N ->
    shortest_tree_on w (all_pairs :\: \bigcup_(j < i) D j) (D i).

Definition ham_path_edges (E : {set V * V}) : Prop :=
  exists (x : V) (p : seq V),
    [/\ uniq (x :: p), size (x :: p) = #|V| & path (fun a b => (a, b) \in E) x p].

End WeightedSpanningTrees.

Definition what_is_the_smallest_number_of_disjoint_spanning_tre_statement : Prop :=
  forall (V : finType) (w : V -> V -> nat),
    (2 <= #|V|)%N -> (forall x y : V, w x y = w y x) ->
    exists (D : nat -> {set V * V}) (k : nat),
      [/\ greedy_decomp w D k,
          ham_path_edges (\bigcup_(j < k) D j) &
          forall k' : nat, (k' < k)%N -> ~ ham_path_edges (\bigcup_(j < k') D j) ].

(** ============================================================================ *)
(** ** Row 2 — Turán number of a finite family

    CARRIER: a finite family of graphs given as [Fam : 'I_k -> sgraph] (indexing by a
    finite ordinal avoids needing [sgraph : eqType] for [\in]-membership), plus the order
    [n].

    AREA-SPECIFIC primitives:
    - [family_free G Fam] : G contains no member of the family as a SUBGRAPH (coq-graph-
      theory's [subgraph], = injective adjacency-preserving embedding);
    - [is_turan_number n Fam m] : m is ex(n,F) — the largest edge count of an n-vertex
      family-free graph (existence of an extremal graph + maximality).

    Conjecture: for every finite (nonempty) family there is a member F0 with
    ex(n,F0) = O(ex(n,F)) — formalised as ∃ C N, ∀ n>=N, ex(n,F0) <= C·ex(n,F). *)

Definition family_free (G : sgraph) (k : nat) (Fam : 'I_k -> sgraph) : Prop :=
  forall i : 'I_k, ~ subgraph (Fam i) G.

Definition is_turan_number (n : nat) (k : nat) (Fam : 'I_k -> sgraph) (m : nat) : Prop :=
  (exists G : sgraph, [/\ #|G| = n, edge_count G = m & family_free G Fam]) /\
  (forall m' : nat,
     (exists G : sgraph, [/\ #|G| = n, edge_count G = m' & family_free G Fam]) ->
     (m' <= m)%N).

Definition turan_number_of_a_finite_family_statement : Prop :=
  forall (k : nat) (Fam : 'I_k -> sgraph), (0 < k)%N ->
    exists (i : 'I_k) (C N : nat),
      forall (n mFam mF0 : nat), (N <= n)%N ->
        is_turan_number n Fam mFam ->
        is_turan_number n (fun _ : 'I_1 => Fam i) mF0 ->
        (mF0 <= C * mFam)%N.

(** ============================================================================ *)
(** ** Row 3 — Good edge labelings

    CARRIER: [sgraph].

    AREA-SPECIFIC primitives:
    - [incr_path l u v p] : [u :: p] is a strictly INCREASING-label path from [u] to [v]
      (consecutive vertices adjacent; the sequence of edge labels strictly increasing);
    - [good_edge_labeling G] : there is a symmetric edge labeling, injective on edges (two
      distinct edges get distinct labels), such that for EVERY ordered pair (u,v) there is
      AT MOST ONE increasing path from u to v;
    - [gel_critical G] : G has NO good edge labeling but every PROPER subgraph does.

    Conjecture (primary): for every c<4 there are only finitely many good-edge-labeling
    critical graphs of average degree < c.  "Finitely many graphs (up to iso)" is rendered
    by a vertex-count bound (for each vertex count there are finitely many graphs); c = a/b
    with a < 4b; "average degree < a/b" is base's [~ average_degree_geq G a b], which
    unfolds to [b·Σ_v deg(v) < a·n] (REUSE of base's average-degree surface). *)

Definition incr_path (G : sgraph) (l : G -> G -> nat) (u v : G) (p : seq G) : bool :=
  [&& uniq (u :: p), path (--) u p, last u p == v,
      sorted ltn (pairmap l u p) & p != [::] ].

Definition good_edge_labeling (G : sgraph) : Prop :=
  exists l : G -> G -> nat,
    [/\ (forall x y : G, l x y = l y x),
        (forall x y x' y' : G,
            x -- y -> x' -- y' -> x != y -> x' != y' ->
            l x y = l x' y' -> [set x; y] == [set x'; y']) &
        (forall (u v : G) (p q : seq G),
            incr_path l u v p -> incr_path l u v q -> p = q) ].

Definition proper_subgraph (H G : sgraph) : Prop := subgraph H G /\ ~ subgraph G H.

Definition gel_critical (G : sgraph) : Prop :=
  ~ good_edge_labeling G /\
  (forall H : sgraph, proper_subgraph H G -> good_edge_labeling H).

Definition good_edge_labelings_statement : Prop :=
  forall a b : nat, (0 < b)%N -> (a < 4 * b)%N ->
    exists N : nat, forall G : sgraph,
      gel_critical G ->
      ~ average_degree_geq G a b ->
      (#|G| <= N)%N.

(** ============================================================================ *)
(** ** Row 4 — Sidorenko's conjecture

    CARRIER: a pair of graphs [H G : sgraph] with [H] bipartite.

    AREA-SPECIFIC primitives:
    - [bipartite G] : the vertices split into two parts with every edge crossing (a proper
      2-colouring);
    - [hom_count H G] : the number of graph HOMOMORPHISMS H → G (adjacency-preserving maps,
      counted over the finite function space [{ffun H -> G}]).

    The bound  hom(H,G) ≥ (2|E(G)|/|V(G)|²)^|E(H)| · |V(G)|^|V(H)|  is stated cross-
    multiplied over [nat] (multiply through by |V(G)|^(2|E(H)|), and 2|E(G)| = [oedges G]):
        (2|E(G)|)^|E(H)| · |V(G)|^|V(H)|  ≤  hom(H,G) · |V(G)|^(2|E(H)|). *)

(** [bipartite] now comes from [GTBase.base] (cross-area finite invariant), in the
    2-colouring form [exists f : G -> bool, forall edge, f x != f y]; imported via base. *)

(** [@MOVE-to-base] [hom_count H G] counts graph homomorphisms.  The set-builder
    predicate [forall x y, (x -- y) ==> (f x -- f y)] is the decidable boolean form of
    base's [is_hom f := forall x y, x -- y -> f x -- f y] (reflected in the grounding
    file as [hom_count_reflects_is_hom]); base provides no boolean [is_homb], so the
    bool is re-spelled here while remaining provably equivalent to base's [is_hom]. *)
Definition hom_count (H G : sgraph) : nat :=
  #|[set f : {ffun H -> G} | [forall x : H, [forall y : H, (x -- y) ==> (f x -- f y)]]]|.

Definition sidorenkos_statement : Prop :=
  forall H G : sgraph, bipartite H -> (0 < #|G|)%N ->
    ((oedges G) ^ (edge_count H) * (#|G|) ^ (#|H|)
       <= hom_count H G * (#|G|) ^ (2 * edge_count H))%N.

(** ============================================================================ *)
(** ** Row 5 — Number of cliques in minor-closed classes

    CARRIER: [sgraph].

    AREA-SPECIFIC primitives:
    - [clique_count G] : the number of (nonempty) cliques = complete subgraphs of G;
    - [Kt_minor_free G t] : G has no K_t minor (negation of coq-graph-theory's [minor]).

    Question: is there a constant c such that every n-vertex K_t-minor-free graph has at
    most c^t·n cliques?  ↦  ∃ c, ∀ t>0 G, K_t-minor-free → clique_count G ≤ c^t · |V(G)|.
    (The [0 < t] guard excludes the vacuous t=0 case: every graph has a [K_0] minor, so
    [Kt_minor_free G 0] is always false.) *)

(** [@MOVE-to-base] *)
Definition clique_count (G : sgraph) : nat :=
  #|[set S : {set G} | cliqueb S && (S != set0)]|.

Definition Kt_minor_free (G : sgraph) (t : nat) : Prop := ~ minor G 'K_t.

Definition number_of_cliques_in_minor_closed_classes_statement : Prop :=
  exists c : nat, forall (t : nat) (G : sgraph), (0 < t)%N ->
    Kt_minor_free G t -> (clique_count G <= c ^ t * #|G|)%N.

(** ============================================================================ *)
(** ** Row 6 — Minimal graphs with a prescribed number of spanning trees

    CARRIER: integers (the quantity [alpha(n)] over [sgraph] witnesses).

    AREA-SPECIFIC primitives:
    - [spanning_tree_count G] : the number τ(G) of spanning trees of G — counted over edge
      subsets [E : {set G * G}] of the adjacency relation that are symmetric, irreflexive,
      span and connect V, and have exactly |V|-1 edges (connected + (n-1) edges ⇔ tree);
    - [is_alpha n k] : k = alpha(n), the least vertex count of a simple graph with exactly
      n spanning trees.

    Conjecture: alpha(n) = o(log n).  Log-free, base-independent eventual form:
        ∀ a b > 0, ∃ N, ∀ n ≥ max(3,N), is_alpha n k → 2^(b·k) < n^a,
    using  k < (a/b)·log₂ n  ⇔  2^(b·k) < n^a. *)

Definition spanning_tree_count (G : sgraph) : nat :=
  #|[set E : {set G * G} |
       [&& [forall p : G * G, (p \in E) ==> (p.1 -- p.2)],
           [forall p : G * G, (p \in E) == ((p.2, p.1) \in E)],
           [forall x : G, (x, x) \notin E],
           [forall x : G, [forall y : G, connect (fun a b => (a, b) \in E) x y]]
         & #|E| == 2 * (#|G|).-1 ] ]|.

Definition is_alpha (n k : nat) : Prop :=
  (exists G : sgraph, #|G| = k /\ spanning_tree_count G = n) /\
  (forall k' : nat,
     (exists G : sgraph, #|G| = k' /\ spanning_tree_count G = n) -> (k <= k')%N).

Definition minimal_graphs_with_a_prescribed_number_of_spanning_statement : Prop :=
  forall a b : nat, (0 < a)%N -> (0 < b)%N ->
    exists N : nat, forall (n k : nat),
      (N <= n)%N -> (3 <= n)%N -> is_alpha n k -> (2 ^ (b * k) < n ^ a)%N.
