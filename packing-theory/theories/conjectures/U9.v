(** * Packing.conjectures.U9 — milestone U9 (namespace Packing, plan v4)

    Statement-only formalizations (axiom-free: no Conjecture/Axiom/Parameter/
    Admitted) of thirteen open problems on packings, partitions, transversals and
    connectivity.

    CARRIERS ARE CHOSEN PER ROW (no blanket [sgraph]), following each row's
    [rocq_idiom] / [selected_proposition]:

      - simple-graph (sgraph) rows: P3-partition (Row 1), triangle packing vs.
        transversal (Row 2), friendly partitions (Row 3), BEC packing (Row 5),
        Lovász path removal (Row 6), Jones (Row 7, PLANAR-gated), odd-cycle
        transversal (Row 8), matching-cut & girth (Row 9), hypercube matchings
        (Row 11), weak saturation (Row 12);
      - multigraph (mgraph = [graph unit unit], with the raw [edge]/[walk]
        /[edges_at]/[source]/[target] API) rows, where the object level is EDGE
        SETS: partitioning edge-connectivity (Row 4), Kriesel trees (Row 10),
        T-join packing (Row 13).

    IMPORT ORDER: [mgraph] is imported BEFORE [base] (base re-exports the sgraph
    vocabulary [sgraph]/[x -- y]/[N(x)]/[connected]/[clique]/[ucycle]/[ucycleb] and
    owns [Delta] (Δ), [regular], [girth_geq]); putting coq-graph-theory's [mgraph]
    first avoids its DIRECTED [line_graph] shadowing base's undirected one (we do
    not use [line_graph] here, but keep the federation-wide ordering invariant).

    REUSED FROM base (NOT redefined): [Delta] (= max-degree Δ, Row 5), [regular]
    (= cubic / r-regular, Rows 1,3), [girth_geq] (Row 9), [clique] (triangles),
    [connected] (induced connectivity), [ucycle]/[ucycleb] (cycles), [N(_)].

    AREA primitives introduced here (packing/partition specific): [is_P3] /
    P3-partition, [is_triangle] / [tri_edges] / triangle-packing /
    triangle-edge-transversal, [friendly_partition] / [all_but_finitely_many_regular],
    [uwalk] (undirected multigraph walk) / [edge_conn_via] / [edge_conn_subset]
    (edge-set-partition-connectivity), [pack]
    (graph-packing), [is_induced_path] (induced-path) / [k_connected] /
    [k_connected_on] (k-connectivity, cross-area @MOVE-to-base candidate),
    [hits_all_cycles] / [is_min_fvs] (feedback-vertex-set) / [cycle_packing] /
    [is_max_cycle_packing] (cycle-packing), [del_bipartite] (edge-odd-cycle-
    transversal) / [triangle_free], [matching_cut] / [avg_deg_lt] (average-degree),
    [acyclic_mg] / [edge_disjoint_uv_paths] / [tree_contains_T] (edge-disjoint
    Steiner trees), [hypercube] (hypercube-graph) / [is_matching_edges] /
    [matching-extension], [copy_Q3_through] / [weakly_saturates] / [is_wsat]
    (weak-saturation-number), [cut_mg] / [is_tjoin] (t-join) / T-cut / graft.

    PLANARITY (Row 7, Jones, [requires_planarity=true]): planarity is the base-
    provided combinatorial predicate [wagner_planar G := ~ minor G 'K_5 /\
    ~ minor G (KB 3 3)] (no K5 / no K3,3 minor).  By Wagner's theorem this IS
    planarity, so Row 7 is now FAITHFUL and Four-Colour-free; [wagner_planar] is
    used opaquely (we do not import [minor]).  The former abstract [planar : sgraph
    -> Prop] placeholder is gone.  All thirteen rows model their statements fully.

    NAMING: predicates use the [is_] prefix ([is_P3], [is_triangle], [is_min_fvs],
    [is_matching_edges], [is_tjoin], [is_wsat]); a trailing [G] ([edge_setG],
    [hamiltonian_cycleG], [cycle_edgesG]) is purely a clash-avoidance suffix (it
    dodges shadowing of upstream names), NOT an arity marker. *)

From GraphTheory Require Import mgraph.
From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ================================================================= *)
(** ** Shared simple-graph primitives *)

(** A path of length 2 (a [P3]): three distinct vertices [x - b - y] with centre
    [b] adjacent to the two ends [x], [y]. *)
Definition is_P3 (G : sgraph) (S : {set G}) : Prop :=
  exists b x y : G,
    [/\ b -- x, b -- y, x != y & S = [set x; b; y]].

(** A triangle: a 3-clique. *)
Definition is_triangle (G : sgraph) (T : {set G}) : Prop :=
  clique T /\ #|T| = 3.

(** The (unordered) edge set of a vertex set [T]: its 2-element subsets.  For a
    clique these are exactly the edges spanned by [T]. *)
Definition tri_edges (G : sgraph) (T : {set G}) : {set {set G}} :=
  [set e : {set G} | (e \subset T) && (#|e| == 2)].

(** The whole-graph edge set (each unordered adjacent pair). *)
Definition edge_setG (G : sgraph) : {set {set G}} :=
  [set e : {set G} | [exists x, exists y, (x -- y) && (e == [set x; y])]].

(** Bipartite after deleting the edge set [S]: a 2-colouring with no
    surviving (non-[S]) edge monochromatic.  "Deleting [S] destroys every odd
    cycle" ⟺ the remaining graph is bipartite. *)
Definition del_bipartite (G : sgraph) (S : {set {set G}}) : Prop :=
  exists A : {set G},
    forall x y : G, x -- y -> [set x; y] \notin S -> (x \in A) != (y \in A).

(** Triangle-free: no 3-clique. *)
(* [triangle_free] now from graph-theory-base (vertex-triple form, equivalent to ~ is_triangle). *)

(** ** k-connectivity (Whitney form, separator-free).  [@MOVE-to-base]: also used
    by hamiltonicity-theory/U2; promote to base when a second area is wired. *)
(* [k_connected] now from graph-theory-base. *)

(** k-connectivity of the induced subgraph on [U] (deletions taken from [U]). *)
Definition k_connected_on (G : sgraph) (U : {set G}) (k : nat) : Prop :=
  (k < #|U|) /\ forall S : {set G}, #|S| < k -> connected (U :\: S).

(** Adjacency of two vertices that are consecutive on the seq [p] (for [uniq p]). *)
Definition consec (G : sgraph) (p : seq G) (a b : G) : bool :=
  ((index a p).+1 == index b p) || ((index b p).+1 == index a p).

(** A simple [x]–[y] path encoded as a vertex seq: nonempty, starts at [x], ends
    at [y], a consecutive-adjacency walk. *)
Definition spath (G : sgraph) (x y : G) (p : seq G) : bool :=
  [&& p != [::], head x p == x, last x p == y & sorted (--) p].

(** An INDUCED [x]–[y] path: a simple path with no chords (any two of its vertices
    adjacent in [G] are consecutive on the path). *)
Definition is_induced_path (G : sgraph) (x y : G) (p : seq G) : Prop :=
  [/\ spath x y p, uniq p
    & {in p &, forall a b : G, a -- b -> consec p a b}].

(** A friendly partition (into [A] and its complement): every vertex has at least
    as many neighbours in its own class as in the other; both classes nonempty. *)
Definition friendly_partition (G : sgraph) (A : {set G}) : Prop :=
  [/\ A != set0, A != [set: G]
    & forall v : G,
        (v \in A -> #|N(v) :&: (~: A)| <= #|N(v) :&: A|) /\
        (v \notin A -> #|N(v) :&: A| <= #|N(v) :&: (~: A)|)].

(** "All but finitely many [r]-regular graphs satisfy [P]": some order threshold
    [N] beyond which every [r]-regular graph satisfies [P].  (Finitely many graphs
    of each order ⇒ this is the faithful "cofinite" reading.) *)
Definition all_but_finitely_many_regular (r : nat) (P : sgraph -> Prop) : Prop :=
  exists N : nat, forall G : sgraph, regular G r -> N < #|G| -> P G.

(** Two same-order graphs PACK: a bijection placing [G1] onto [G2]'s vertices with
    no edge of [G1] landing on an edge of [G2] (edge-disjoint placement). *)
Definition pack (G1 G2 : sgraph) : Prop :=
  exists f : G1 -> G2,
    bijective f /\ forall x y : G1, x -- y -> ~~ (f x -- f y).

(** A matching-cut: a bipartition [{A, ~A}] (both nonempty) whose crossing edges
    form a matching — every vertex has at most one neighbour on the other side. *)
Definition matching_cut (G : sgraph) : Prop :=
  exists A : {set G},
    [/\ A != set0, A != [set: G]
      & forall v : G,
          (v \in A -> #|N(v) :&: (~: A)| <= 1) /\
          (v \notin A -> #|N(v) :&: A| <= 1)].

(** Average degree strictly below [d]: ∑deg < d·n (avoids fractions). *)
Definition avg_deg_lt (G : sgraph) (d : nat) : Prop :=
  (\sum_(v : G) #|N(v)|) < d * #|G|.

(** ** Feedback vertex sets and cycle packings *)

(** [X] meets every genuine cycle (size > 2); i.e. [G - X] is acyclic. *)
Definition hits_all_cycles (G : sgraph) (X : {set G}) : Prop :=
  forall c : seq G, ucycle (--) c -> 2 < size c -> exists2 v : G, v \in c & v \in X.

(** [m] is the minimum feedback-vertex-set size cc(G). *)
Definition is_min_fvs (G : sgraph) (m : nat) : Prop :=
  (exists X : {set G}, hits_all_cycles X /\ #|X| = m) /\
  (forall X : {set G}, hits_all_cycles X -> m <= #|X|).

(** A cycle packing: a list of genuine cycles, pairwise vertex-disjoint (each
    vertex on at most one of them). *)
Definition cycle_packing (G : sgraph) (cs : seq (seq G)) : Prop :=
  (forall c : seq G, c \in cs -> ucycle (--) c /\ 2 < size c) /\
  (forall v : G, count (fun c => v \in c) cs <= 1).

(** [m] is the maximum cycle-packing size cp(G). *)
Definition is_max_cycle_packing (G : sgraph) (m : nat) : Prop :=
  (exists cs : seq (seq G), cycle_packing cs /\ size cs = m) /\
  (forall cs : seq (seq G), cycle_packing cs -> size cs <= m).

(** ** Hamiltonicity on simple graphs (Row 11).  [@MOVE-to-base]: cross-area
    (hamiltonicity-theory/U2 owns the same notion) — promote when a 2nd consumer
    is wired, mirroring the [k_connected] precedent. *)
Definition hamiltonian_cycleG (G : sgraph) (c : seq G) : bool :=
  ucycleb (--) c && (size c == #|G|).
Arguments hamiltonian_cycleG : clear implicits.

Definition cycle_edgesG (G : sgraph) (c : seq G) : {set {set G}} :=
  [set [set x; next c x] | x in [set z | z \in c]].
Arguments cycle_edgesG : clear implicits.

(** A set of edges that is a matching: each element is a genuine edge, and every
    vertex lies in at most one of them. *)
Definition is_matching_edges (G : sgraph) (M : {set {set G}}) : Prop :=
  (forall e : {set G}, e \in M -> exists x y : G, x -- y /\ e = [set x; y]) /\
  (forall v : G, #|[set e in M | v \in e]| <= 1).

(** ** The hypercube graph Q_d (Hamming graph on d-bit strings) *)
Section Hypercube.
Variable d : nat.
Definition hc_rel : rel (d.-tuple bool) :=
  fun x y => #|[set i : 'I_d | tnth x i != tnth y i]| == 1.
Lemma hc_sym : symmetric hc_rel.
Proof.
move=> x y; rewrite /hc_rel.
have -> : [set i : 'I_d | tnth x i != tnth y i]
        = [set i : 'I_d | tnth y i != tnth x i]
  by apply/setP=> i; rewrite !inE eq_sym.
by [].
Qed.
Lemma hc_irrefl : irreflexive hc_rel.
Proof.
move=> x; rewrite /hc_rel.
have -> : [set i : 'I_d | tnth x i != tnth x i] = set0
  by apply/setP=> i; rewrite !inE eqxx.
by rewrite cards0.
Qed.
Definition hypercube : sgraph := SGraph hc_sym hc_irrefl.
End Hypercube.

(** ** Weak saturation of Q_3 in K_n (Row 12)

    Vertices of K_n are ['I_n]; a "graph on K_n" is an edge set
    [E : {set {set 'I_n}}] of 2-subsets.  A copy of [Q_3] in [E] is an injective
    embedding of [hypercube 3] mapping its edges into [E]. *)

(** A copy of Q_3 inside the edge set [E] that USES the edge [e]
    (i.e. some Q_3-edge maps onto [e]). *)
Definition copy_Q3_through (n : nat) (E : {set {set 'I_n}}) (e : {set 'I_n}) : Prop :=
  exists f : hypercube 3 -> 'I_n,
    [/\ injective f,
        (forall x y : hypercube 3, x -- y -> [set f x; f y] \in E)
      & (exists x y : hypercube 3, x -- y /\ [set f x; f y] = e)].

(** [F] is weakly Q_3-saturating in K_n: [F] is a graph on K_n, and its missing
    edges can be enumerated [s] so that adding each [s_i] (to [F] together with all
    earlier additions, including [s_i]) completes a new Q_3 copy through [s_i]. *)
Definition weakly_saturates (n : nat) (F : {set {set 'I_n}}) : Prop :=
  (forall e : {set 'I_n}, e \in F -> #|e| == 2) /\
  exists s : seq {set 'I_n},
    [/\ uniq s,
        (forall e : {set 'I_n}, (e \in s) = ((#|e| == 2) && (e \notin F)))
      & (forall i : nat, i < size s ->
           copy_Q3_through (F :|: [set x in take i.+1 s]) (nth set0 s i))].

(** [m] is the weak-saturation number wsat(K_n, Q_3): least edge count of a weakly
    Q_3-saturating graph. *)
Definition is_wsat (n : nat) (m : nat) : Prop :=
  (exists F : {set {set 'I_n}}, weakly_saturates F /\ #|F| = m) /\
  (forall F : {set {set 'I_n}}, weakly_saturates F -> m <= #|F|).

(** ================================================================= *)
(** ** Shared multigraph primitives (edge-set object level) *)

(** An UNDIRECTED walk in a multigraph: each step may traverse an edge in either
    orientation (the library [walk] only goes [source -> target], which on the
    DIRECTED carrier [mgraph = graph unit unit] would encode directed/strong
    reachability — wrong for the undirected "edge-connected graph" of Row 4). *)
(* [uwalk] (undirected multigraph walk) now from graph-theory-base. *)

(** Connectivity using only the edges of [E]: any two vertices joined by an
    UNDIRECTED [E]-walk (undirected edge-connectivity, faithful to Row 4). *)
Definition edge_conn_via (G : mgraph) (E : {set edge G}) : Prop :=
  forall x y : G, exists w : seq (edge G),
    uwalk x y w /\ all (fun e => e \in E) w.

(** The spanning subgraph [(V, E)] is [a]-edge-connected: deleting fewer than [a]
    of its edges keeps it (spanning-)connected. *)
Definition edge_conn_subset (G : mgraph) (E : {set edge G}) (a : nat) : Prop :=
  forall F : {set edge G}, F \subset E -> #|F| < a -> edge_conn_via (E :\: F).

(** A forest / acyclic edge set: every nonempty subset has a vertex of odd degree
    (equivalently, trivial binary cycle space). *)
Definition acyclic_mg (G : mgraph) (H : {set edge G}) : Prop :=
  forall C : {set edge G}, C \subset H -> C != set0 ->
    exists v : G, odd #|edges_at v :&: C|.

(** [m] pairwise edge-disjoint [u]–[v] walks (an [m]-flow of edge-disjoint paths). *)
Definition edge_disjoint_uv_paths (G : mgraph) (u v : G) (m : nat) : Prop :=
  exists ws : seq (seq (edge G)),
    [/\ size ws = m,
        (forall w : seq (edge G), w \in ws -> walk u v w)
      & (forall e : edge G, count (fun w => e \in w) ws <= 1)].

(** A tree (acyclic edge set) that contains / connects [T]: every two vertices of
    [T] are joined by an [H]-walk. *)
Definition tree_contains_T (G : mgraph) (T : {set G}) (H : {set edge G}) : Prop :=
  acyclic_mg H /\
  (forall x y : G, x \in T -> y \in T ->
     exists w : seq (edge G), walk x y w /\ all (fun e => e \in H) w).

(** The edge cut of a vertex set [S]: edges with exactly one endpoint in [S]. *)
Definition cut_mg (G : mgraph) (S : {set G}) : {set edge G} :=
  [set e | (source e \in S) (+) (target e \in S)].

(** A [T]-join: an edge set whose odd-degree vertices are exactly [T]. *)
Definition is_tjoin (G : mgraph) (T : {set G}) (J : {set edge G}) : Prop :=
  forall v : G, odd #|edges_at v :&: J| = (v \in T).

(** ================================================================= *)
(** ** Row 1 — Partition of cubic 3-connected graphs into paths of length 2  (OPEN)

    Source: "Problem: Does every 3-connected cubic graph on 3k vertices admit a
    partition into k paths of length 2?"

    Carrier: [sgraph].  cubic = [regular G 3] (base); 3-connected = [k_connected G 3];
    a "path of length 2" is a [P3] ([is_P3]); the partition's blocks are exactly the
    [k] paths.  Guard [0 < k] excludes the degenerate empty partition. *)
Definition partition_of_a_cubic_3_connected_graphs_into_paths_o_statement : Prop :=
  forall (k : nat) (G : sgraph),
    0 < k -> regular G 3 -> k_connected G 3 -> #|G| = 3 * k ->
    exists P : {set {set G}},
      [/\ partition P [set: G],
          (forall S : {set G}, S \in P -> is_P3 S)
        & #|P| = k].

(** ** Row 2 — Triangle packing vs. triangle edge transversal  (OPEN)

    Source: "Conjecture: If G has at most k edge-disjoint triangles, then there is
    a set of 2k edges whose deletion destroys every triangle."

    Carrier: [sgraph] (edges as 2-subsets).  Hypothesis: every set of pairwise
    edge-disjoint triangles has size ≤ k (triangle-packing ≤ k).  Conclusion: a
    triangle-edge-transversal [S] of ≤ 2k edges meeting every triangle. *)
Definition triangle_packing_vs_triangle_edge_transversal_statement : Prop :=
  forall (k : nat) (G : sgraph),
    (forall P : {set {set G}},
       (forall T : {set G}, T \in P -> is_triangle T) ->
       {in P &, forall T1 T2 : {set G},
          T1 != T2 -> [disjoint tri_edges T1 & tri_edges T2]} ->
       #|P| <= k) ->
    exists S : {set {set G}},
      #|S| <= 2 * k /\
      (forall T : {set G}, is_triangle T ->
         exists2 e : {set G}, e \in tri_edges T & e \in S).

(** ** Row 3 — Friendly partitions  (OPEN)

    Source: "A friendly partition of a graph is a partition of the vertices into
    two sets so that every vertex has at least as many neighbours in its own class
    as in the other.  Problem: Is it true that for every r, all but finitely many
    r-regular graphs have friendly partitions?"

    Carrier: [sgraph].  "All but finitely many [r]-regular graphs" =
    [all_but_finitely_many_regular] (an order threshold). *)
Definition friendly_partitions_statement : Prop :=
  forall r : nat,
    all_but_finitely_many_regular r
      (fun G => exists A : {set G}, friendly_partition A).

(** ** Row 4 — Partitioning edge connectivity  (OPEN)

    Source: "Question: Let G be an (a+b+2)-edge-connected graph.  Does there exist
    a partition {A,B} of E(G) so that (V,A) is a-edge-connected and (V,B) is
    b-edge-connected?"

    Carrier: [mgraph] (edge sets).  Whole-graph (a+b+2)-edge-connectivity is
    [edge_conn_subset [set: edge G] (a+b+2)]; the spanning subgraphs [(V,A)],
    [(V,B)] reuse the same primitive on the edge subsets. *)
Definition partitioning_edge_connectivity_statement : Prop :=
  forall (a b : nat) (G : mgraph),
    0 < #|G| -> edge_conn_subset [set: edge G] (a + b + 2) ->
    exists A B : {set edge G},
      [/\ A :|: B = [set: edge G], [disjoint A & B],
          edge_conn_subset A a & edge_conn_subset B b].

(** ** Row 5 — Bollobás–Eldridge–Catlin (BEC) packing conjecture  (OPEN)

    Source: "Conjecture (BEC-conjecture): If G1 and G2 are n-vertex graphs and
    (Δ(G1)+1)(Δ(G2)+1) < n+1, then G1 and G2 pack."

    Carrier: a pair of [sgraph]s on a common order [n].  Δ = base [Delta]
    (max-degree, REUSED); packing = [pack] (edge-disjoint placement). *)
Definition the_bollobas_eldridge_catlin_conjecture_on_graph_pac_statement : Prop :=
  forall (n : nat) (G1 G2 : sgraph),
    #|G1| = n -> #|G2| = n ->
    (Delta G1 + 1) * (Delta G2 + 1) < n + 1 ->
    pack G1 G2.

(** ** Row 6 — Lovász path-removal conjecture  (OPEN)

    Source: "Conjecture: There is an integer-valued function f(k) such that if G is
    any f(k)-connected graph and x and y are any two vertices of G, then there
    exists an induced path P with ends x and y such that G−V(P) is k-connected."

    Carrier: [sgraph].  [is_induced_path] (induced-path); [k_connected] /
    [k_connected_on] (k-connectivity); the removed vertex set is [V(P)]. *)
Definition lovasz_path_removal_statement : Prop :=
  exists f : nat -> nat,
    forall (k : nat) (G : sgraph) (x y : G),
      x != y -> k_connected G (f k) ->
      exists p : seq G,
        is_induced_path x y p /\
        k_connected_on ([set: G] :\: [set z in p]) k.

(** ** Row 7 — Jones' conjecture  (OPEN — PLANAR, FAITHFUL)

    Source: "For a graph G, let cp(G) denote the cardinality of a maximum cycle
    packing (collection of vertex disjoint cycles) and let cc(G) denote the
    cardinality of a minimum feedback vertex set (set of vertices X so that G−X is
    acyclic).  Conjecture: For every planar graph G, cc(G) ≤ 2·cp(G)."

    Carrier: [sgraph].  PLANARITY is now the base-provided combinatorial predicate
    [wagner_planar G := ~ minor G 'K_5 /\ ~ minor G (KB 3 3)] (no K5 and no K3,3
    minor).  By Wagner's theorem this IS planarity, so the row is FAITHFUL and
    Four-Colour-free; [wagner_planar] is used opaquely (we do not import [minor]).
    The former abstract [forall planar : sgraph -> Prop] placeholder is gone.
    cc = [is_min_fvs] (feedback-vertex-set); cp = [is_max_cycle_packing]
    (cycle-packing), both stated relationally (no min/max existence proof needed). *)
Definition jones_statement : Prop :=
  forall (G : sgraph) (ccn cpn : nat),
    wagner_planar G -> is_min_fvs G ccn -> is_max_cycle_packing G cpn ->
    ccn <= 2 * cpn.

(** ** Row 8 — Odd cycle transversal in triangle-free graphs  (OPEN)

    Source: "Conjecture: If G is a simple triangle-free graph, then there is a set
    of at most n²/25 edges whose deletion destroys every odd cycle."

    Carrier: [sgraph].  [triangle_free]; the transversal [S] is a set of edges with
    [#|S| ≤ n²/25] whose removal makes the graph bipartite ([del_bipartite]). *)
Definition odd_cycle_transversal_in_triangle_free_graphs_statement : Prop :=
  forall G : sgraph,
    triangle_free G ->
    exists S : {set {set G}},
      [/\ S \subset edge_setG G,
          #|S| <= (#|G| ^ 2) %/ 25
        & del_bipartite S].

(** ** Row 9 — Matching-cut and girth  (OPEN)

    Source: "Question: For every d does there exists a g such that every graph with
    average degree smaller than d and girth at least g has a matching-cut?"

    Carrier: [sgraph].  average degree < d = [avg_deg_lt]; girth ≥ g = base
    [girth_geq] (REUSED); [matching_cut]. *)
Definition matching_cut_and_girth_statement : Prop :=
  forall d : nat, exists g : nat,
    forall G : sgraph,
      0 < #|G| -> avg_deg_lt G d -> girth_geq G g -> matching_cut G.

(** ** Row 10 — Kriesel's conjecture  (OPEN)

    Source: "Conjecture: Let G be a graph and let T ⊆ V(G) such that for any pair
    u,v ∈ T there are 2k edge-disjoint paths from u to v in G.  Then G contains k
    edge-disjoint trees, each of which contains T."

    Carrier: [mgraph].  Hypothesis: [edge_disjoint_uv_paths u v (2*k)] for every
    pair in [T] (edge-disjoint-paths-count).  Conclusion: [k] pairwise
    edge-disjoint trees each connecting [T] (edge-disjoint Steiner trees).  Guard
    [0 < k] excludes the boundary-trivial [k = 0] case (empty witnesses). *)
Definition kriesells_statement : Prop :=
  forall (G : mgraph) (T : {set G}) (k : nat),
    0 < #|G| -> 0 < k ->
    (forall u v : G, u \in T -> v \in T -> edge_disjoint_uv_paths u v (2 * k)) ->
    exists Ts : seq {set edge G},
      [/\ size Ts = k,
          (forall Ti : {set edge G}, Ti \in Ts -> tree_contains_T T Ti)
        & (forall e : edge G, count (fun Ti : {set edge G} => e \in Ti) Ts <= 1)].

(** ** Row 11 — Matchings extend to Hamilton cycles in hypercubes  (OPEN)

    Source: "Question: Does every matching of hypercube extend to a Hamiltonian
    cycle?"

    Carrier: the [hypercube] graph Q_d.  [is_matching_edges] (matching as an edge
    set); extension = a Hamilton cycle whose edge set contains [M]
    (matching-extension).  Guard [2 ≤ d] (Q_0/Q_1 have no Hamilton cycle). *)
Definition matchings_extends_to_hamilton_cycles_in_hypercubes_statement : Prop :=
  forall (d : nat) (M : {set {set hypercube d}}),
    2 <= d -> is_matching_edges M ->
    exists c : seq (hypercube d),
      hamiltonian_cycleG (hypercube d) c /\
      M \subset cycle_edgesG (hypercube d) c.

(** ** Row 12 — Weak saturation of the cube in the clique  (OPEN)

    Source: "Problem: Determine wsat(K_n, Q_3)."

    Carrier: graphs on K_n = edge sets over ['I_n]; Q_3 = [hypercube 3].  A
    "Determine X" problem is formalized as well-definedness of the quantity:
    wsat(K_n, Q_3) is a well-defined number ([is_wsat], the least weakly
    Q_3-saturating edge count).  Guard [8 ≤ n] (need ≥ |V(Q_3)| = 8 vertices). *)
Definition weak_saturation_of_the_cube_in_the_clique_statement : Prop :=
  forall n : nat, 8 <= n -> exists m : nat, is_wsat n m.

(** ** Row 13 — Packing T-joins  (OPEN)

    Source: "Conjecture: There exists a fixed constant c (probably c=1 suffices) so
    that every graft with minimum T-cut size at least k contains a T-join packing
    of size at least (2/3)k − c."

    Carrier: a graft [(G, T)] with [G : mgraph] and [T] of even size.  min T-cut ≥ k:
    every [S] with [#|S ∩ T|] odd has cut size ≥ k (t-cut).  Conclusion: [m]
    pairwise edge-disjoint [T]-joins (t-join packing) with [2k ≤ 3(m+c)]
    (= [m ≥ (2/3)k − c], fraction-free).  Guard [0 < #|T|] excludes the degenerate
    empty graft ([T = set0], where the cut hypothesis is vacuous and [J = set0]
    repeated trivially satisfies the bound). *)
Definition packing_t_joins_statement : Prop :=
  exists c : nat,
    forall (G : mgraph) (T : {set G}) (k : nat),
      0 < #|G| -> 0 < #|T| -> ~~ odd #|T| ->
      (forall S : {set G}, odd #|S :&: T| -> k <= #|cut_mg S|) ->
      exists (Js : seq {set edge G}) (m : nat),
        [/\ size Js = m,
            (forall J : {set edge G}, J \in Js -> is_tjoin T J),
            (forall e : edge G, count (fun J : {set edge G} => e \in J) Js <= 1)
          & 2 * k <= 3 * (m + c)].
