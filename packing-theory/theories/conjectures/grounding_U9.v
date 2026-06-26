(** * Packing.conjectures.grounding_U9 — grounding lemmas for milestone U9.

    SIMPLE, Qed-closed sanity results validating the NEW primitives introduced
    in [U9.v] (packings / partitions / transversals / connectivity vocabulary).
    For each new definition we record a SATISFIABLE witness and at least one
    textbook identity.  These are statement-VALIDATION lemmas, NOT the (open)
    conjectures themselves.

    Two tiny concrete carriers are used for the simple-graph witnesses:
      - [En n] : the edgeless ("empty") graph on ['I_n];
      - [Kn n] : the complete graph on ['I_n].
    The edge-set / multigraph primitives are validated abstractly (over an
    arbitrary [G : mgraph]) via degenerate ([set0] / vacuous) witnesses. *)

From GraphTheory Require Import mgraph.
From GTBase Require Import base.
From Packing.conjectures Require Import U9.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ============================================================================
    Tiny concrete carriers.
    ========================================================================== *)

Section EmptyGraph.
Variable n : nat.
Definition En_rel : rel 'I_n := fun _ _ => false.
Lemma En_sym : symmetric En_rel. Proof. by []. Qed.
Lemma En_irr : irreflexive En_rel. Proof. by []. Qed.
Definition En : sgraph := SGraph En_sym En_irr.
End EmptyGraph.

Lemma En_edge (n : nat) (x y : En n) : (x -- y) = false.
Proof. by []. Qed.

Lemma En_N (n : nat) (v : En n) : N(v) = set0.
Proof. by apply/setP=> u; rewrite !inE; apply: En_edge. Qed.

Section CompleteGraph.
Variable n : nat.
Definition Kn_rel : rel 'I_n := fun x y => x != y.
Lemma Kn_sym : symmetric Kn_rel. Proof. by move=> x y; rewrite /Kn_rel eq_sym. Qed.
Lemma Kn_irr : irreflexive Kn_rel. Proof. by move=> x; rewrite /Kn_rel eqxx. Qed.
Definition Kn : sgraph := SGraph Kn_sym Kn_irr.
End CompleteGraph.

Lemma Kn_edge (n : nat) (x y : Kn n) : (x -- y) = (x != y).
Proof. by []. Qed.

(** Three distinct vertices of [Kn 3]. *)
Definition v0 : Kn 3 := @Ordinal 3 0 isT.
Definition v1 : Kn 3 := @Ordinal 3 1 isT.
Definition v2 : Kn 3 := @Ordinal 3 2 isT.

Lemma v0n1 : v0 != v1. Proof. by rewrite -val_eqE. Qed.
Lemma v0n2 : v0 != v2. Proof. by rewrite -val_eqE. Qed.
Lemma v1n2 : v1 != v2. Proof. by rewrite -val_eqE. Qed.

(** A generic single-vertex "no other vertex" lemma: a singleton is not the
    whole vertex set as soon as a second vertex exists. *)
Lemma set1_neqT (G : sgraph) (x0 y0 : G) : x0 != y0 -> [set x0] != [set: G].
Proof.
by move=> H; apply/eqP => e; move: (in_setT y0); rewrite -e inE eq_sym (negbTE H).
Qed.

(** ============================================================================
    [is_P3] / [is_triangle] / [tri_edges] / [edge_setG].
    ========================================================================== *)

(** witness: [Kn 3] has a triangle on its whole vertex set. *)
Lemma is_triangle_witness : is_triangle [set: Kn 3].
Proof.
split; last by rewrite cardsT card_ord.
by move=> x y _ _ ne; rewrite Kn_edge.
Qed.

(** identity: a triangle has exactly three vertices. *)
Lemma is_triangle_card (G : sgraph) (T : {set G}) : is_triangle T -> #|T| = 3.
Proof. by case. Qed.

(** witness: [Kn 3] contains the [P3] [v0 - v1 - v2]. *)
Lemma is_P3_witness : is_P3 (G := Kn 3) [set v0; v1; v2].
Proof.
exists v1, v0, v2; split; rewrite ?Kn_edge -?val_eqE //.
Qed.

(** identity: a [P3] is nonempty (its centre belongs to it). *)
Lemma is_P3_neq0 (G : sgraph) (S : {set G}) : is_P3 S -> S != set0.
Proof.
case=> b [x] [y] [_ _ _ ->]; apply/set0Pn; exists b.
by rewrite !inE eqxx orbT.
Qed.

(** identity: every element of [tri_edges T] is a 2-set inside [T]. *)
Lemma tri_edges_card (G : sgraph) (T e : {set G}) :
  e \in tri_edges T -> #|e| = 2.
Proof. by rewrite inE => /andP[_ /eqP]. Qed.

Lemma tri_edges_sub (G : sgraph) (T e : {set G}) :
  e \in tri_edges T -> e \subset T.
Proof. by rewrite inE => /andP[]. Qed.

(** identity: a 2-subset of [T] is one of its [tri_edges]. *)
Lemma tri_edges_mem (G : sgraph) (T : {set G}) (a b : G) :
  a != b -> [set a; b] \subset T -> [set a; b] \in tri_edges T.
Proof. by move=> ab sub; rewrite inE sub cards2 ab. Qed.

(** identity: adjacency characterises membership in the whole-graph edge set. *)
Lemma edge_setG_mem (G : sgraph) (x y : G) :
  x -- y -> [set x; y] \in edge_setG G.
Proof.
move=> xy; rewrite inE; apply/existsP; exists x; apply/existsP; exists y.
by rewrite xy eqxx.
Qed.

Lemma edge_setG_inv (G : sgraph) (e : {set G}) :
  e \in edge_setG G -> exists x y : G, (x -- y) /\ e = [set x; y].
Proof.
rewrite inE => /existsP[x] /existsP[y] /andP[xy /eqP ->].
by exists x, y.
Qed.

(** ============================================================================
    [del_bipartite] / [triangle_free].
    ========================================================================== *)

(** witness: deleting ALL edges destroys every odd cycle (the graph becomes
    edgeless, hence bipartite). *)
Lemma del_bipartite_full (G : sgraph) : del_bipartite (edge_setG G).
Proof.
exists set0 => x y xy; by rewrite (edge_setG_mem xy).
Qed.

(** identity: a graph with fewer than three vertices is triangle-free. *)
Lemma triangle_free_small (G : sgraph) : #|G| < 3 -> triangle_free G.
Proof.
move=> hG T [_ hT].
have h2 := subset_leq_card (subsetT T); rewrite cardsT hT in h2.
by move: (leq_ltn_trans h2 hG); rewrite ltnn.
Qed.

(** witness: the 2-vertex edgeless graph is triangle-free. *)
Lemma triangle_free_witness : triangle_free (En 2).
Proof. by apply: triangle_free_small; rewrite card_ord. Qed.

(** ============================================================================
    [k_connected] / [k_connected_on].
    ========================================================================== *)

(** identity: [k]-connectivity needs more than [k] vertices. *)
Lemma k_connected_card (G : sgraph) (k : nat) : k_connected G k -> k < #|G|.
Proof. by case. Qed.

(** witness: every nonempty graph is 0-connected. *)
Lemma k_connected0 (G : sgraph) : 0 < #|G| -> k_connected G 0.
Proof. by move=> h; split=> // S; rewrite ltn0. Qed.

Lemma k_connected_on_card (G : sgraph) (U : {set G}) (k : nat) :
  k_connected_on U k -> k < #|U|.
Proof. by case. Qed.

(** ============================================================================
    [spath] / [consec] / [is_induced_path].
    ========================================================================== *)

(** witness: the trivial one-vertex path is an induced path from [x] to [x]. *)
Lemma is_induced_path_triv (G : sgraph) (x : G) : is_induced_path x x [:: x].
Proof.
split.
- by rewrite /spath /= !eqxx.
- by [].
- by move=> a b; rewrite !inE => /eqP-> /eqP->; rewrite sg_irrefl.
Qed.

(** identity: an induced path is in particular an [spath] with distinct vertices. *)
Lemma is_induced_path_spath (G : sgraph) (x y : G) (p : seq G) :
  is_induced_path x y p -> spath x y p /\ uniq p.
Proof. by case=> sp up _. Qed.

(** ============================================================================
    [friendly_partition] / [all_but_finitely_many_regular].
    ========================================================================== *)

Definition u0 : En 2 := @Ordinal 2 0 isT.
Definition u1 : En 2 := @Ordinal 2 1 isT.
Lemma u0n1 : u0 != u1. Proof. by rewrite -val_eqE. Qed.

(** witness: in an edgeless graph EVERY non-trivial cut is friendly. *)
Lemma friendly_partition_witness : friendly_partition (G := En 2) [set u0].
Proof.
split.
- by apply/set0Pn; exists u0; rewrite inE eqxx.
- by apply: set1_neqT; exact: u0n1.
- by move=> v; rewrite En_N !set0I !cards0; split.
Qed.

(** identity: a friendly partition is a genuine bipartition (both parts present). *)
Lemma friendly_partition_proper (G : sgraph) (A : {set G}) :
  friendly_partition A -> A != set0 /\ A != [set: G].
Proof. by case. Qed.

(** witness: "all but finitely many [r]-regular graphs satisfy [True]". *)
Lemma abfm_True (r : nat) : all_but_finitely_many_regular r (fun _ => True).
Proof. by exists 0. Qed.

(** identity: the cofinite-regular quantifier is monotone in its predicate. *)
Lemma abfm_mono (r : nat) (P Q : sgraph -> Prop) :
  (forall G, P G -> Q G) ->
  all_but_finitely_many_regular r P -> all_but_finitely_many_regular r Q.
Proof. by move=> PQ [N hN]; exists N => G rG NG; apply/PQ/hN. Qed.

(** ============================================================================
    [pack].
    ========================================================================== *)

(** witness: an edgeless graph packs with itself (place via the identity). *)
Lemma pack_witness (n : nat) : pack (En n) (En n).
Proof.
by exists id; split; [exact: preliminaries.id_bij | move=> x y; rewrite En_edge].
Qed.

(** ============================================================================
    [matching_cut] / [avg_deg_lt].
    ========================================================================== *)

(** witness: the 2-vertex edgeless graph has a matching-cut. *)
Lemma matching_cut_witness : matching_cut (En 2).
Proof.
exists [set u0]; split.
- by apply/set0Pn; exists u0; rewrite inE eqxx.
- by apply: set1_neqT; exact: u0n1.
- by move=> v; rewrite En_N !set0I !cards0; split.
Qed.

(** identity: an edgeless graph has zero total degree, hence average degree
    below any positive [d] (as soon as it is nonempty). *)
Lemma avg_deg_lt_witness (n : nat) : 0 < n -> avg_deg_lt (En n) 1.
Proof.
move=> n0; rewrite /avg_deg_lt.
rewrite (eq_bigr (fun=> 0)) => [|v _]; last by rewrite En_N cards0.
by rewrite big_const iter_addn_0 mul0n mul1n card_ord.
Qed.

(** ============================================================================
    [hits_all_cycles] / [is_min_fvs] / [cycle_packing] / [is_max_cycle_packing].
    ========================================================================== *)

(** A cycle visits genuine vertices: the edgeless 0-vertex graph has none. *)
Lemma En0_no_long (c : seq (En 0)) : 2 < size c -> False.
Proof. by case: c => [|x c'] // _; case: x. Qed.

(** witness: the full vertex set meets every cycle. *)
Lemma hits_all_cycles_full (G : sgraph) : hits_all_cycles (setT : {set G}).
Proof.
move=> c _ sz; case: c sz => [|a c'] // _.
by exists a; [exact: mem_head | exact: in_setT].
Qed.

(** witness: in the empty (vertexless) graph the minimum FVS is 0. *)
Lemma is_min_fvs_witness : is_min_fvs (En 0) 0.
Proof.
split.
- exists set0; split; last exact: cards0.
  by move=> c _ /En0_no_long.
- by move=> X _; exact: leq0n.
Qed.

(** identity: a minimum FVS is realised by some hitting set of that size. *)
Lemma is_min_fvs_inv (G : sgraph) (m : nat) :
  is_min_fvs G m -> exists X : {set G}, hits_all_cycles X /\ #|X| = m.
Proof. by case. Qed.

(** witness: the empty list is always a cycle packing. *)
Lemma cycle_packing_nil (G : sgraph) : cycle_packing (G := G) [::].
Proof. by split=> // c; rewrite in_nil. Qed.

(** witness: in the empty (vertexless) graph the maximum cycle packing is 0. *)
Lemma is_max_cycle_packing_witness : is_max_cycle_packing (En 0) 0.
Proof.
split.
- by exists [::]; split=> //; exact: cycle_packing_nil.
- case=> [|c0 cs'] // [H _].
  by case: (H c0 (mem_head _ _)) => _ /En0_no_long.
Qed.

(** identity: every genuine cycle in a packing has more than two vertices. *)
Lemma cycle_packing_long (G : sgraph) (cs : seq (seq G)) (c : seq G) :
  cycle_packing cs -> c \in cs -> 2 < size c.
Proof. by case=> H _ /H[]. Qed.

(** ============================================================================
    [hamiltonian_cycleG] / [cycle_edgesG] / [is_matching_edges].
    ========================================================================== *)

(** witness: the triangle [Kn 3] has a Hamiltonian cycle. *)
Lemma hamiltonian_cycleG_witness :
  hamiltonian_cycleG (Kn 3) [:: v0; v1; v2].
Proof.
rewrite /hamiltonian_cycleG; apply/andP; split; last by rewrite /= card_ord.
by rewrite /ucycleb /=.
Qed.

(** identity: a Hamiltonian cycle is a spanning cycle (length = order). *)
Lemma hamiltonian_cycleG_size (G : sgraph) (c : seq G) :
  hamiltonian_cycleG G c -> size c = #|G|.
Proof. by rewrite /hamiltonian_cycleG => /andP[_ /eqP]. Qed.

(** witness: the empty edge set is a matching. *)
Lemma is_matching_edges_nil (G : sgraph) : is_matching_edges (set0 : {set {set G}}).
Proof.
split=> [e|v]; first by rewrite in_set0.
have ->: [set e in (set0 : {set {set G}}) | v \in e] = set0
  by apply/setP=> e; rewrite !inE andFb.
by rewrite cards0.
Qed.

(** identity: every edge of a matching is a genuine edge. *)
Lemma is_matching_edges_edge (G : sgraph) (M : {set {set G}}) (e : {set G}) :
  is_matching_edges M -> e \in M -> exists x y : G, (x -- y) /\ e = [set x; y].
Proof. by case=> H _ /H. Qed.

(** ============================================================================
    [hypercube].
    ========================================================================== *)

(** identity: the [d]-cube has [2^d] vertices. *)
Lemma card_hypercube (d : nat) : #|hypercube d| = 2 ^ d.
Proof. by rewrite card_tuple card_bool. Qed.

(** ============================================================================
    [copy_Q3_through] / [weakly_saturates] / [is_wsat].
    ========================================================================== *)

(** identity: the edge a Q_3-copy is routed through belongs to the host graph. *)
Lemma copy_Q3_through_mem (n : nat) (E : {set {set 'I_n}}) (e : {set 'I_n}) :
  copy_Q3_through E e -> e \in E.
Proof. by case=> f [_ hE [x [y [xy <-]]]]; apply: hE. Qed.

(** witness: the complete graph on [K_n] (all 2-subsets) is weakly saturating —
    it has no missing edge, so the saturation sequence is empty. *)
Lemma weakly_saturates_complete (n : nat) :
  weakly_saturates [set e : {set 'I_n} | #|e| == 2].
Proof.
split=> [e|]; first by rewrite inE.
exists [::]; split=> // e.
by rewrite in_nil inE; case: (#|e| == 2).
Qed.

(** identity: a weak-saturation number is realised by some saturating graph. *)
Lemma is_wsat_inv (n m : nat) :
  is_wsat n m -> exists F : {set {set 'I_n}}, weakly_saturates F /\ #|F| = m.
Proof. by case. Qed.

(** ============================================================================
    Multigraph primitives: [uwalk] / [edge_conn_via] / [edge_conn_subset] /
    [acyclic_mg] / [edge_disjoint_uv_paths] / [tree_contains_T] / [cut_mg] /
    [is_tjoin].
    ========================================================================== *)

(** identity: the empty undirected walk witnesses reflexivity of connectivity. *)
Lemma uwalk_nil (G : mgraph) (x : G) : uwalk x x [::].
Proof. by rewrite /= eqxx. Qed.

(** identity (undirectedness): a single edge is walkable in BOTH orientations. *)
Lemma uwalk_fwd (G : mgraph) (e : edge G) : uwalk (source e) (target e) [:: e].
Proof. by rewrite /= !eqxx. Qed.

Lemma uwalk_bwd (G : mgraph) (e : edge G) : uwalk (target e) (source e) [:: e].
Proof. by rewrite /= !eqxx orbT. Qed.

(** witness: every edge set is 0-edge-connectivity-robust (vacuously). *)
Lemma edge_conn_subset0 (G : mgraph) (E : {set edge G}) : edge_conn_subset E 0.
Proof. by move=> F _; rewrite ltn0. Qed.

(** identity: positive edge-connectivity entails plain connectivity. *)
Lemma edge_conn_subset_via (G : mgraph) (E : {set edge G}) (a : nat) :
  0 < a -> edge_conn_subset E a -> edge_conn_via E.
Proof.
move=> a0 H; move: (H set0 (sub0set _)).
by rewrite cards0 setD0 => /(_ a0).
Qed.

(** witness: the empty edge set is acyclic. *)
Lemma acyclic_mg_nil (G : mgraph) : acyclic_mg (set0 : {set edge G}).
Proof. by move=> C; rewrite subset0 => /eqP ->; rewrite eqxx. Qed.

(** identity: acyclicity is hereditary (a subset of a forest is a forest). *)
Lemma acyclic_mg_sub (G : mgraph) (H H' : {set edge G}) :
  H' \subset H -> acyclic_mg H -> acyclic_mg H'.
Proof. by move=> sub aH C CH'; apply: aH; exact: subset_trans CH' sub. Qed.

(** witness: there are always 0 edge-disjoint [u]-[v] paths. *)
Lemma edge_disjoint_uv_paths0 (G : mgraph) (u v : G) :
  edge_disjoint_uv_paths u v 0.
Proof. by exists [::]. Qed.

(** witness: the empty tree connects the empty terminal set. *)
Lemma tree_contains_T_nil (G : mgraph) :
  tree_contains_T (set0 : {set G}) (set0 : {set edge G}).
Proof. by split; [exact: acyclic_mg_nil | move=> x y; rewrite in_set0]. Qed.

(** identity: a tree-connecting set is in particular acyclic. *)
Lemma tree_contains_T_acyclic (G : mgraph) (T : {set G}) (H : {set edge G}) :
  tree_contains_T T H -> acyclic_mg H.
Proof. by case. Qed.

(** identity: the empty vertex set has an empty cut. *)
Lemma cut_mg0 (G : mgraph) : cut_mg (set0 : {set G}) = set0.
Proof. by apply/setP=> e; rewrite !inE addbb. Qed.

(** witness: the empty edge set is a [set0]-join. *)
Lemma is_tjoin_nil (G : mgraph) : is_tjoin (set0 : {set G}) (set0 : {set edge G}).
Proof. by move=> v; rewrite setI0 cards0 in_set0. Qed.

(** identity: a [T]-join's odd-degree vertices are exactly [T]. *)
Lemma is_tjoin_charact (G : mgraph) (T : {set G}) (J : {set edge G}) :
  is_tjoin T J -> T = [set v | odd #|edges_at v :&: J|].
Proof. by move=> HJ; apply/setP=> v; rewrite inE HJ. Qed.


