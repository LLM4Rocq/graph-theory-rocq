(** * Digraph.conjectures.P9 — milestone P9 (plan v4), namespace [Digraph]

    Statement-only (axiom-free) formalisation of 20 open OPG digraph
    conjectures/problems. Each node is a [Definition <formal_name> : Prop],
    carrier type chosen per the manifest's [rocq_idiom] (tournament /
    orientedDigraph / diGraphType, never a blanket undirected [sgraph]).

    The file REUSES the existing directed core and the already-committed
    conjecture primitives wherever possible:
      - core/{digraph,oriented,tournament,dipath,strong}: [arc], [outdeg],
        [outdeg_in], [outsel], [dipath], [dicycle], [strongb], [induced_digraph],
        [del_vertex], [dgiso], [sub_tournament], [TT], [converse], [next];
      - conjectures/classic_core: [stable], [indeg], [diregular]
        (note: [indeg] is defined in BOTH classic_core and colouring_variants,
         so use sites below qualify it as [classic_core.indeg] — a base-reuse
         duplication to be consolidated to one canonical in-degree at G3);
      - conjectures/chi_bounded: [underlying] (the underlying simple graph of a
        digraph) and graph-theory's ordinary chromatic number [χ(_)] (row 18);
      - conjectures/dichromatic: [acyclicb], [dicolorableb];
      - conjectures/packing: [real_sel], [selindeg], [arc_disjoint_sel],
        [out_branching], [in_branching];
      - conjectures/colouring_variants: [oriented_kcolouring],
        [mono_reach_or_rainbow_statement] (row 3), [dhom];
      - conjectures/two_extremal: [loopless], [underlyingG], [planar_sg]
        (the repo's Wagner-minor combinatorial planarity, so the three
        planarity rows compile in this switch WITHOUT coq-fourcolor).

    Three nodes are aliases onto already-present constants (no restating):
    [hoand_reed_statement] (= packing.hoang_reed_statement),
    [hamilton_cycle_in_small_d_diregular_graphs_statement]
    (= classic_core.jackson_hamilton_small_diregular_statement) and
    [monochromatic_reachability_vs_rainbow_triangles_statement]
    (= colouring_variants.mono_reach_or_rainbow_statement). *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph oriented tournament dipath strong.
From Digraph Require Import classic_core dichromatic packing colouring_variants two_extremal.
From Digraph Require Import interop_graph_theory chi_bounded.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Shared NEW primitives — base candidates, to migrate at G3

    BASE-MOVE: every general, conjecture-agnostic primitive in this section is a
    candidate for relocation to the directed base on the G3 base move:
      - invariant-style scalars/predicates ([nb_arcs], [weakly_connected],
        [tree_digraph], [cyc_arcs], [ham], [kstrong], [arccut], [karcstrong],
        [alpha], [cyclomatic]/[nb_wcc]/[wadj], [dipath_arcs], [arcset_outdeg],
        [arcset_indeg], [single_dicycle_arcset], [ndicycles], [nonedge_count],
        [short_dicycle_free], [set_partition], [arc_decomp])
        -> theories/invariants/ at G3;
    Each is greppable via the "BASE-MOVE:" tag. NB: [alpha]/[stable]/[indeg]
    collide with GraphTheory.core.dom and the classic_core/colouring_variants
    duplicate of [indeg]; the move must pick one canonical name and qualify. *)

(* BASE-MOVE: relocate to theories/invariants/ at G3 (general diGraph primitives). *)
Section Primitives.
Variable D : diGraphType.
Implicit Types (v w : D) (c : seq D) (f : D -> {set D}).

(** Number of arcs of [D] (ordered head/tail pairs). *)
Definition nb_arcs : nat := #|[set p : D * D | p.1 --> p.2]|.

(** Weak connectivity: reachability under the symmetric closure of [arc]. *)
Definition weakly_connected : bool :=
  [forall u : D, [forall v : D, connect (fun x y : D => (x --> y) || (y --> x)) u v]].

(** Underlying undirected tree: weakly connected with [#V - 1] arcs. (On an
    oriented digraph arcs are in bijection with the underlying edges, so this is
    "the underlying graph is a tree".) *)
Definition tree_digraph : bool := weakly_connected && (nb_arcs == #|D| - 1).

(** Arc set [{(u,v) : u\in c, v = next}] traversed by a directed cycle [c]
    (the EDGES of the cycle, for arc-/edge-disjointness). *)
Definition cyc_arcs c : {set D * D} :=
  [set p : D * D | (p.1 \in c) && (next c p.1 == p.2)].

(** A Hamiltonian directed cycle: a [dicycle] through every vertex. *)
Definition ham c : bool := dicycle c && (size c == #|D|).

(** Vertex [k]-strong connectivity: more than [k] vertices and removing any set
    of fewer than [k] vertices leaves a strongly connected digraph. *)
Definition kstrong (k : nat) : bool :=
  (k < #|D|) && [forall S : {set D}, (#|S| < k) ==> strongb (induced_digraph (~: S))].

(** Number of forward-crossing arcs out of [B] (its out-cut). *)
Definition arccut (B : {set D}) : nat :=
  #|[set p : D * D | [&& p.1 \in B, p.2 \notin B & p.1 --> p.2]]|.

(** [k]-arc-strong connectivity: every nonempty proper [B] has out-cut ≥ [k]
    (Menger form of arc-connectivity ≥ [k]). Guard [1 < #|D|] (not just [0 < #|D|])
    so the predicate is non-vacuous: on a 1-vertex digraph there is no nonempty
    proper [B], which would make every [k] hold. *)
Definition karcstrong (k : nat) : bool :=
  (1 < #|D|) && [forall B : {set D}, ((B != set0) && (B != [set: D])) ==> (k <= arccut B)].

(** Independence number α(D): largest [stable] (arc-free) vertex set. *)
Definition alpha : nat := \max_(S : {set D} | stable S) #|S|.

(** Spanning CYCLIC subdigraph as an arc selector [f]: real arcs only and every
    vertex has positive kept in- and out-degree (so every vertex lies on a
    cycle of the kept subdigraph). *)
Definition cyclic_sel f : bool :=
  real_sel f && [forall v : D, (0 < #|f v|) && (0 < selindeg f v)].

(** Cyclomatic number (circuit rank) of an arc selector [f]: [m + c - n] with
    [m] kept arcs, [c] weakly-connected components, [n = #V]. *)
Definition wadj f : rel D := fun u w => (w \in f u) || (u \in f w).
Definition nb_wcc f : nat := #|[set [set y | connect (wadj f) x y] | x in [set: D]]|.
Definition cyclomatic f : nat := (\sum_(v : D) #|f v|) + nb_wcc f - #|D|.

(** Arcs of a directed path [x :: s] (consecutive vertex pairs). *)
Definition dipath_arcs (x : D) (s : seq D) : {set D * D} := [set p in zip (x :: s) s].

(** Out-/in-degree of a vertex inside a fixed arc set [A]. *)
Definition arcset_outdeg (A : {set D * D}) v : nat := #|[set w | (v, w) \in A]|.
Definition arcset_indeg (A : {set D * D}) v : nat := #|[set u | (u, v) \in A]|.

(** [A] is the arc set of a SINGLE directed cycle: nonempty, all real arcs,
    in-degree = out-degree ≤ 1 at every vertex, and its support is connected
    (so it is one cycle, not a union of several). *)
Definition single_dicycle_arcset (A : {set D * D}) : bool :=
  [&& A != set0,
      [forall p : D * D, (p \in A) ==> (p.1 --> p.2)],
      [forall v : D, (arcset_outdeg A v == arcset_indeg A v) && (arcset_outdeg A v <= 1)] &
      [forall u : D, [forall w : D,
         ((0 < arcset_outdeg A u) && (0 < arcset_outdeg A w)) ==>
         connect (fun a b : D => (a, b) \in A) u w]]].

(** Number of directed cycles of [D] (counted by their arc sets). *)
Definition ndicycles : nat := #|[set A : {set D * D} | single_dicycle_arcset A]|.

(** Number of NON-EDGES: unordered nonadjacent vertex pairs. *)
Definition nonedge_count : nat :=
  #|[set e : {set D} | (#|e| == 2) && [forall u in e, [forall v in e, ~~ (u --> v)]]]|.

(** No directed cycle of length ≤ 3 (no loop, no digon, no directed triangle). *)
Definition short_dicycle_free : bool :=
  [&& [forall u : D, ~~ (u --> u)],
      [forall u : D, [forall v : D, ~~ ((u --> v) && (v --> u))]] &
      [forall u : D, [forall v : D, [forall w : D, ~~ [&& u --> v, v --> w & w --> u]]]]].

(** A vertex partition (each vertex in exactly one part). *)
Definition set_partition (part : seq {set D}) : bool :=
  [forall v : D, count (fun A : {set D} => v \in A) part == 1].

(** An arc decomposition by selectors [fs]: real arcs only, every arc kept by
    exactly one selector. *)
Definition arc_decomp (fs : seq (D -> {set D})) : bool :=
  all (@real_sel D) fs &&
  [forall e : D * D, (\sum_(f <- fs) (e.2 \in f e.1)) == (e.1 --> e.2)].

End Primitives.

(** ** Subdigraph containment and subdivision *)

(* BASE-MOVE: relocate to theories/core or theories/invariants at G3. *)
(** [D] contains [H] as a subdigraph: an injective arc-preserving map. *)
Definition contains_subdig (D H : diGraphType) : Prop :=
  exists phi : H -> D, injective phi /\ (forall u v : H, u --> v -> phi u --> phi v).

(** [D] contains a SUBDIVISION of [H]: injective branch vertices [b] and, for
    every arc [u --> v] of [H], an internally-disjoint directed path of [D] from
    [b u] to [b v] avoiding all other branch vertices. *)
Definition subdivides (D H : diGraphType) : Prop :=
  exists (b : H -> D) (p : H -> H -> seq D),
    [/\ injective b,
        (forall u v : H, u --> v -> dipath (b u) (p u v) /\ last (b u) (p u v) = b v),
        (forall u v : H, u --> v -> forall x : H, b x \notin behead (belast (b u) (p u v))) &
        (forall u v u' v' : H, u --> v -> u' --> v' -> (u != u') || (v != v') ->
           ~~ has (mem (behead (belast (b u') (p u' v'))))
                  (behead (belast (b u) (p u v))))].

(** ** Oriented / antidirected trees (orientations of trees) *)

Definition oriented_tree (T : orientedDigraph) : bool := tree_digraph T.

Definition antidirected_tree (T : orientedDigraph) : bool :=
  (* [classic_core.indeg] qualified: [indeg] is declared in both classic_core and
     colouring_variants (base-reuse duplicate, to consolidate at G3). *)
  tree_digraph T && [forall v : T, (outdeg v == 0) || (classic_core.indeg v == 0)].

(** ** Switching of digraphs (Seidel-style switching reconstruction) *)

(* BASE-MOVE: relocate to theories/constructions/ at G3. *)
(** [switched S]: reverse every arc with exactly one endpoint in [S]. *)
Definition switched (D : diGraphType) (S : {set D}) : Type := D.
Section Switched.
Variables (D : diGraphType) (S : {set D}).
HB.instance Definition _ := Finite.on (switched S).
HB.instance Definition _ :=
  HasArc.Build (switched S) (fun u v : D => if (u \in S) (+) (v \in S) then arc v u else arc u v).
End Switched.

(** Switching equivalence: isomorphic after switching on some vertex set. *)
Definition sw_iso (D1 D2 : diGraphType) : Prop := exists S : {set D1}, dgiso (switched S) D2.

(** Same switching deck: a vertex bijection matching the switching classes of
    all vertex-deleted cards. *)
Definition same_deck (D1 D2 : diGraphType) : Prop :=
  exists g : D1 -> D2, bijective g /\ forall i : D1, sw_iso (del_vertex i) (del_vertex (g i)).

(** Switching-reconstructible: determined up to switching by its deck. *)
Definition switching_reconstructible (D : diGraphType) : Prop :=
  forall D' : diGraphType, same_deck D D' -> sw_iso D D'.

(** ** Arc removal / arc reversal (for feedback sets and Ádám's conjecture) *)

(* BASE-MOVE: relocate to theories/constructions/ at G3. *)
(** [remove_arcs F]: [D] with the arcs in [F] deleted. *)
Definition remove_arcs (D : diGraphType) (F : {set D * D}) : Type := D.
Section RemoveArcs.
Variables (D : diGraphType) (F : {set D * D}).
HB.instance Definition _ := Finite.on (remove_arcs F).
HB.instance Definition _ :=
  HasArc.Build (remove_arcs F) (fun u v : D => (u --> v) && ((u, v) \notin F)).
End RemoveArcs.

(* BASE-MOVE: relocate to theories/invariants/ at G3 (general diGraph invariant). *)
(** [F] is a feedback arc set iff deleting it makes [D] acyclic; the minimum
    feedback-arc-set size [β(D)]. *)
Definition min_feedback (D : diGraphType) : nat :=
  #|[arg min_(F < [set: D * D] | acyclicb (remove_arcs F)) #|F|]|.

(* BASE-MOVE: relocate to theories/constructions/ at G3. *)
(** [rev_arc a]: [D] with the single arc [a] reversed (a tournament stays a
    tournament; modelled at digraph level). *)
Definition rev_arc (D : diGraphType) (a : D * D) : Type := D.
Section RevArc.
Variables (D : diGraphType) (a : D * D).
HB.instance Definition _ := Finite.on (rev_arc a).
HB.instance Definition _ :=
  HasArc.Build (rev_arc a)
    (fun u v : D => if (u == a.1) && (v == a.2) then false
                    else if (u == a.2) && (v == a.1) then true else u --> v).
End RevArc.

(** ** Transitive triangles [TT3] for arc-disjoint packings *)

(** A transitive subtournament of order 3: [a --> b], [b --> c], [a --> c]. *)
Definition tt3 (T : tournament) (t : T * T * T) : bool :=
  [&& t.1.1 --> t.1.2, t.1.2 --> t.2 & t.1.1 --> t.2].

(** Its three arcs. *)
Definition tt3_arcs (T : tournament) (t : T * T * T) : {set T * T} :=
  [set (t.1.1, t.1.2); (t.1.2, t.2); (t.1.1, t.2)].

(** ** The 20 milestone statements ****************************************** *)

(** *** Row 1 — minimum number of arc-disjoint transitive subtournaments TT3.
    A tournament of order [n] contains ⌈n(n−1)/6 − n/3⌉ = ⌈n(n−3)/6⌉ pairwise
    arc-disjoint transitive triangles. *)
Definition minimum_number_of_transitive_subtournaments_of_order_statement : Prop :=
  forall T : tournament, 3 <= #|T| ->
    exists P : seq (T * T * T),
      [/\ all (@tt3 T) P,
          pairwise (fun a b => [disjoint tt3_arcs a & tt3_arcs b]) P &
          (#|T| * (#|T| - 3) + 5) %/ 6 <= size P].

(** *** Row 2 — cyclic spanning subdigraph with small cyclomatic number.
    If all strong components are nontrivial (equivalently every vertex lies on a
    directed cycle), [D] has a cyclic spanning subdigraph with cyclomatic number
    at most α(D). *)
Definition cyclic_spanning_subdigraph_with_small_cyclomatic_num_statement : Prop :=
  forall D : diGraphType,
    (forall v : D, exists c : seq D, dicycle c /\ v \in c) ->
    exists f : D -> {set D}, cyclic_sel f /\ (cyclomatic f <= alpha D).

(** *** Row 3 — monochromatic reachability vs rainbow triangles (alias).
    Reuses [colouring_variants.mono_reach_or_rainbow_statement]. *)
Definition monochromatic_reachability_vs_rainbow_triangles_statement : Prop :=
  mono_reach_or_rainbow_statement.

(** *** Row 4 — subdivision of a transitive tournament under large outdegree.
    There is [f] so that minimum out-degree ≥ [f(k)] forces a subdivision of the
    transitive tournament [TT k]. *)
Definition subdivision_of_a_transitive_tournament_in_digraphs_w_statement : Prop :=
  exists f : nat -> nat,
    forall (k : nat) (D : diGraphType),
      (forall v : D, f k <= outdeg v) -> subdivides D (TT k : diGraphType).

(** *** Row 5 — antidirected trees in dense digraphs.
    If [|A(D)| > (k−2)|V(D)|] then [D] contains every antidirected tree of order
    [k]. *)
Definition antidirected_trees_in_digraphs_statement : Prop :=
  forall (D : diGraphType) (k : nat), 2 <= k ->
    (k - 2) * #|D| < nb_arcs D ->
    forall T : orientedDigraph, antidirected_tree T -> #|T| = k -> contains_subdig D T.

(** *** Row 6 — edge-disjoint Hamilton cycles in highly strong tournaments.
    For every [k ≥ 2] some [f(k)] makes every [f(k)]-strong tournament have [k]
    arc-disjoint Hamilton cycles. *)
Definition edge_disjoint_hamilton_cycles_statement : Prop :=
  forall k : nat, 2 <= k ->
    exists f : nat -> nat,
      forall T : tournament, kstrong T (f k) ->
        exists Cs : seq (seq T),
          [/\ all (@ham T) Cs,
              pairwise (fun a b => [disjoint cyc_arcs a & cyc_arcs b]) Cs &
              size Cs = k].

(** *** Row 7 — partitioning planar digraphs (PLANARITY).
    An orientation of a simple planar graph partitions into two acyclic induced
    subdigraphs. Planarity is the repo's Wagner-minor [planar_sg] of the
    underlying simple graph. *)
Definition partitioning_planar_digraphs_statement : Prop :=
  forall (D : diGraphType) (llD : loopless D),
    (forall u v : D, u --> v -> ~~ (v --> u)) ->
    planar_sg (underlyingG llD) ->
    exists X : {set D}, acyclicb (induced_digraph X) /\ acyclicb (induced_digraph (~: X)).

(** *** Row 8 — partitioning a tournament into k strongly connected parts.
    There is [g(k_1,…,k_p)] so every [g]-strong tournament partitions into parts
    [V_i] each inducing a nontrivial [k_i]-strong subtournament. *)
Definition partitionning_a_tournament_into_k_strongly_connected_statement : Prop :=
  exists g : seq nat -> nat,
    forall ks : seq nat, all (fun k => 0 < k) ks ->
      forall T : tournament, kstrong T (g ks) ->
        exists part : seq {set T},
          [/\ size part = size ks, set_partition part &
              forall i : 'I_(size ks),
                (1 < #|nth set0 part i|) /\
                kstrong (sub_tournament (nth set0 part i)) (nth 0 ks i)].

(** *** Row 9 — switching reconstruction of digraphs.
    Encodes the open question affirmatively: some digraph on ≥ 12 vertices is
    switching-nonreconstructible. *)
Definition switching_reconstruction_of_digraphs_statement : Prop :=
  exists D : diGraphType, (12 <= #|D|) /\ ~ switching_reconstructible D.

(** *** Row 10 — arc-disjoint directed cycles in regular digraphs.
    A [k]-regular digraph (no parallel arcs) has [C(k+1,2)] arc-disjoint
    directed cycles. *)
Definition arc_disjoint_directed_cycles_in_regular_directed_gra_statement : Prop :=
  forall (D : diGraphType) (k : nat), diregular D k ->
    exists P : seq (seq D),
      [/\ all (@dicycle D) P,
          pairwise (fun a b => [disjoint cyc_arcs a & cyc_arcs b]) P &
          'C(k.+1, 2) <= size P].

(** *** Row 11 — decomposing an even tournament into directed paths.
    A tournament on an even number of vertices decomposes into
    [∑_v max(0, d⁺(v) − d⁻(v))] directed paths. *)
Definition decomposing_an_even_tournament_in_directed_paths_statement : Prop :=
  forall T : tournament, ~~ odd #|T| ->
    exists Q : seq (T * seq T),
      [/\ all (fun p => dipath p.1 p.2) Q,
          [forall e : T * T, (\sum_(p <- Q) (e \in dipath_arcs p.1 p.2)) == (e.1 --> e.2)] &
          size Q = \sum_(v : T) (outdeg v - classic_core.indeg v)].

(** *** Row 12 — Hoàng–Reed (alias onto [packing.hoang_reed_statement]). *)
Definition hoand_reed_statement : Prop := hoang_reed_statement.

(** *** Row 13 — arc-disjoint out-branching and in-branching.
    Some [k] makes every [k]-arc-strong digraph (with chosen [u], [v]) contain an
    out-branching at [u] and an in-branching at [v] that are arc-disjoint. *)
Definition arc_disjoint_out_branching_and_in_branching_statement : Prop :=
  exists k : nat,
    forall (D : diGraphType) (u v : D), karcstrong D k ->
      exists f g : D -> {set D},
        [/\ out_branching f u, in_branching g v & arc_disjoint_sel f g].

(** *** Row 14 — decomposing a k-arc-strong tournament into k spanning strong
    subdigraphs. *)
Definition decomposing_k_arc_strong_tournament_into_k_spanning_statement : Prop :=
  forall (T : tournament) (k : nat), 0 < k -> karcstrong T k ->
    exists fs : seq (T -> {set T}),
      [/\ size fs = k, arc_decomp fs & all (fun f => strongb (outsel f)) fs].

(** *** Row 15 — non-edges vs feedback edge sets.
    A simple digraph with no directed cycle of length ≤ 3 has
    [β(G) ≤ ½·γ(G)], i.e. [2·β(G) ≤ γ(G)]. *)
Definition non_edges_vs_feedback_edge_sets_in_digraphs_statement : Prop :=
  forall D : diGraphType, short_dicycle_free D -> 2 * min_feedback D <= nonedge_count D.

(** *** Row 16 — Hamilton cycle in small d-diregular oriented graphs
    (alias onto [classic_core.jackson_hamilton_small_diregular_statement]). *)
Definition hamilton_cycle_in_small_d_diregular_graphs_statement : Prop :=
  jackson_hamilton_small_diregular_statement.

(** *** Row 17 — oriented chromatic number of planar graphs (PLANARITY).
    The maximum oriented chromatic number over oriented planar graphs is a
    well-defined value [M]: it bounds all of them and is attained. *)
Definition oriented_chromatic_number_of_planar_graphs_statement : Prop :=
  exists M : nat,
    (forall (D : diGraphType) (llD : loopless D),
        (forall u v : D, u --> v -> ~~ (v --> u)) ->
        planar_sg (underlyingG llD) -> oriented_kcolouring D M) /\
    (exists (D : diGraphType) (llD : loopless D),
        [/\ (forall u v : D, u --> v -> ~~ (v --> u)),
            planar_sg (underlyingG llD) & ~ oriented_kcolouring D M.-1]).

(** *** Row 18 — oriented trees in n-chromatic digraphs (Burr).
    Every digraph whose UNDERLYING undirected graph has ordinary chromatic number
    χ ≥ 2k−2 contains every oriented tree of order [k]. The chromatic number is the
    GRAPH-THEORY [χ(_)] of the underlying simple graph [underlying D] (Gallai–Roy /
    Burr lineage), NOT the dichromatic number χ⃗ — an earlier draft used
    [~~ dicolorableb D (2*k-3)] which is the dichromatic reading and, since χ⃗ ≤ χ,
    encoded a strictly weaker statement (faithfulness fix). *)
Definition oriented_trees_in_n_chromatic_digraphs_statement : Prop :=
  forall (D : diGraphType) (k : nat), 2 <= k ->
    (2 * k - 2 <= χ([set: underlying D]))%N ->
    forall T : orientedDigraph, oriented_tree T -> #|T| = k -> contains_subdig D T.

(** *** Row 19 — Ádám's conjecture (tournament case, open).
    Every tournament with a directed cycle has an arc whose reversal strictly
    reduces the number of directed cycles. *)
Definition adams_statement : Prop :=
  forall T : tournament, (exists c : seq T, dicycle c) ->
    exists a : T * T, (a.1 --> a.2) /\ (ndicycles (rev_arc a) < ndicycles T).

(** *** Row 20 — large acyclic induced subdigraph in a planar oriented graph
    (PLANARITY).  A planar oriented graph has an acyclic induced subdigraph of
    order ≥ (3/5)|V|, i.e. [5·#S ≥ 3·#V]. *)
Definition large_acyclic_induced_subdigraph_in_a_planar_oriente_statement : Prop :=
  forall (D : diGraphType) (llD : loopless D),
    (forall u v : D, u --> v -> ~~ (v --> u)) ->
    planar_sg (underlyingG llD) ->
    exists S : {set D}, acyclicb (induced_digraph S) /\ (3 * #|D| <= 5 * #|S|).
