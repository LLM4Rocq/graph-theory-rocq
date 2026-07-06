(** * Cycle.conjectures.grounding_U6 — grounding lemmas for milestone U6

    Qed-closed, axiom-free sanity results for the new primitives introduced in
    [Cycle.conjectures.U6].  For each primitive we provide:
      - a SATISFIABLE witness (the predicate is inhabited / non-contradictory);
      - at least one textbook IDENTITY it must satisfy.

    Witness models used:
      - [Gd]: the digon (2 vertices, 2 oppositely-oriented parallel edges) — a
        genuine nonempty circuit / 2-factor / eulerian multigraph; grounds the
        structural primitives ([is_circuit], [two_factor], [cdc], ...).
      - [U]: a single vertex, no edges — grounds the connectivity /
        empty-decomposition primitives.
      - [void_graph]: no vertices — grounds the spanning/2-factor primitives
        vacuously.

    NOTE on directed walks: U6's [walk] traverses edges source->target, so an
    [is_circuit] needs oppositely-oriented edges (the digon), and [is_path] /
    [two_connected] have no cheap concrete nonempty witness; for those we record
    structural identities / teeth.  [cubic] is grounded by a two-vertex graph
    with three parallel non-loop edges. *)

From GraphTheory Require Import mgraph.
From GTBase Require Import base.
From Cycle.conjectures Require Import U6.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** The digon witness graph [Gd] *)

Definition G0 : mgraph := two_graph tt tt.
Definition G1 : mgraph := mgraph.add_edge G0 (inl tt) (inr tt) tt.
Definition Gd : mgraph := mgraph.add_edge G1 (inr tt) (inl tt) tt.
Definition G2p : mgraph := mgraph.add_edge G1 (inl tt) (inr tt) tt.
Definition G3p : mgraph := mgraph.add_edge G2p (inl tt) (inr tt) tt.

(** Trivial witness graphs: one vertex (no edges) and the empty graph. *)
Definition U : mgraph := unit_graph tt.
Definition V : mgraph := void_graph unit unit.

Lemma card_edge_Gd : #|edge Gd| = 2.
Proof. by rewrite /Gd /G1 /G0 !card_option card_sum !card_void. Qed.

Lemma card_edge_G3p : #|edge G3p| = 3.
Proof. by rewrite /G3p /G2p /G1 /G0 !card_option card_sum !card_void. Qed.

Lemma inc_all (v : Gd) (e : edge Gd) : incident v e.
Proof.
rewrite /incident; apply/existsP.
by case: v => -[]; case: e => [[[[]|[]]|]|];
  [exists false|exists true|exists true|exists false].
Qed.

Lemma inc_all_G3p (v : G3p) (e : edge G3p) : incident v e.
Proof.
rewrite /incident; apply/existsP.
by case: v => -[]; case: e => [[[[[]|[]]|]|]|];
  [exists false|exists false|exists false|exists true|exists true|exists true].
Qed.

Lemma edges_at_Gd (v : Gd) : edges_at v = [set: edge Gd].
Proof. by apply/setP => e; rewrite !inE inc_all. Qed.

Lemma edges_at_G3p (v : G3p) : edges_at v = [set: edge G3p].
Proof. by apply/setP => e; rewrite !inE inc_all_G3p. Qed.

Lemma subdeg_Gd (H : {set edge Gd}) (v : Gd) : subdeg H v = #|H|.
Proof. by rewrite /subdeg edges_at_Gd setTI. Qed.

Lemma mdeg_Gd (v : Gd) : mdeg v = 2.
Proof. by rewrite /mdeg edges_at_Gd cardsT card_edge_Gd. Qed.

Lemma mdeg_G3p (v : G3p) : mdeg v = 3.
Proof. by rewrite /mdeg edges_at_G3p cardsT card_edge_G3p. Qed.

(** ** [subdeg] / [mdeg] : identities *)

Lemma subdeg_set0 (G : mgraph) (v : G) : subdeg (@set0 (edge G)) v = 0.
Proof. by rewrite /subdeg setI0 cards0. Qed.

Lemma subdeg_setT (G : mgraph) (v : G) : subdeg [set: edge G] v = mdeg v.
Proof. by rewrite /subdeg /mdeg setIT. Qed.

Lemma subdeg_le_mdeg (G : mgraph) (H : {set edge G}) (v : G) :
  (subdeg H v <= mdeg v)%N.
Proof. by rewrite /subdeg /mdeg subset_leq_card // subsetIl. Qed.

(** ** [subgraph_kregular] : witness + identity *)

Lemma subgraph_kregular_set0 (G : mgraph) (k : nat) :
  subgraph_kregular (@set0 (edge G)) k.
Proof. by move=> v; left; rewrite subdeg_set0. Qed.

Lemma two_factor_kregular (G : mgraph) (F : {set edge G}) :
  two_factor F -> subgraph_kregular F 2.
Proof. by move=> H v; right; rewrite H. Qed.

Lemma subgraph_kregular_Gd : subgraph_kregular (G:=Gd) [set: edge Gd] 2.
Proof. by move=> v; right; rewrite subdeg_Gd cardsT card_edge_Gd. Qed.

(** ** [two_factor] : witness (void) + identity, and the digon 2-factor *)

Lemma two_factor_void : two_factor (@set0 (edge (V))).
Proof. by case. Qed.

Lemma two_factor_Gd : two_factor (G:=Gd) [set: edge Gd].
Proof. by move=> v; rewrite subdeg_Gd cardsT card_edge_Gd. Qed.

(** ** [even_subgraph] : witness + identity *)

Lemma even_subgraph_set0 (G : mgraph) : even_subgraph (@set0 (edge G)).
Proof. by move=> v; rewrite subdeg_set0. Qed.

Lemma two_factor_even (G : mgraph) (F : {set edge G}) :
  two_factor F -> even_subgraph F.
Proof. by move=> H v; rewrite H. Qed.

Lemma even_subgraph_Gd : even_subgraph (G:=Gd) [set: edge Gd].
Proof. by move=> v; rewrite subdeg_Gd cardsT card_edge_Gd. Qed.

(** ** [walk_in] : witness + identity (reflexive empty walk) *)

Lemma walk_in_nil (G : mgraph) (H : {set edge G}) (x : G) : walk_in H x x [::].
Proof. by rewrite /walk_in /= eqxx. Qed.

(** ** [mconnected] : witness *)

Lemma mconnected_unit : mconnected (U).
Proof. by move=> x y; exists [::]; case: x; case: y. Qed.

(** ** [connected_del_edges] / [connected_del_verts] : witnesses *)

Lemma connected_del_edges_unit :
  connected_del_edges (G:=U) set0.
Proof. by move=> x y; exists [::]; split; [case: x; case: y|]. Qed.

Lemma connected_del_verts_unit :
  connected_del_verts (G:=U) set0.
Proof. by move=> x y _ _; exists [::]; split; [case: x; case: y|]. Qed.

(** ** [two_connected] : identity + teeth *)

Lemma two_connected_card (G : mgraph) : two_connected G -> (3 <= #|G|)%N.
Proof. by case. Qed.

Lemma not_two_connected_unit : ~ two_connected U.
Proof. by move=> /two_connected_card; rewrite card_unit. Qed.

(** ** [edge_connected] : witness (vacuous at k=0) + identity *)

Lemma edge_connected0 (G : mgraph) : edge_connected G 0.
Proof. by move=> E; rewrite ltn0. Qed.

(** ** [H_inc] / [subgraph_connected] : identity + witness *)

Lemma H_inc_set0 (G : mgraph) (x : G) : H_inc (@set0 (edge G)) x = false.
Proof. by apply: negbTE; apply/existsPn => e; rewrite in_set0. Qed.

Lemma subgraph_connected_set0 (G : mgraph) :
  subgraph_connected (@set0 (edge G)).
Proof. by move=> x y; rewrite H_inc_set0. Qed.

Lemma subgraph_connected_Gd : subgraph_connected (G:=Gd) [set: edge Gd].
Proof.
move=> x y _ _; case: x => -[]; case: y => -[].
- by exists [::].
- by exists [:: Some None]; rewrite /walk_in /= !inE.
- by exists [:: None]; rewrite /walk_in /= !inE.
- by exists [::].
Qed.

(** ** [is_circuit] : witness (digon) + identity *)

Lemma is_circuit_neq0 (G : mgraph) (C : {set edge G}) :
  is_circuit C -> C != set0.
Proof. by case. Qed.

Lemma is_circuit_Gd : is_circuit (G:=Gd) [set: edge Gd].
Proof.
split.
- by rewrite -card_gt0 cardsT card_edge_Gd.
- exact: subgraph_kregular_Gd.
- exact: subgraph_connected_Gd.
Qed.

(** ** [acyclic] : witness + identity *)

Lemma acyclic_set0 (G : mgraph) : acyclic (@set0 (edge G)).
Proof.
move=> C; rewrite subset0 => /eqP ->.
by case=> Hne _ _; move: Hne; rewrite eqxx.
Qed.

(** ** [is_path] : identity (no cheap nonempty witness, directed walks) *)

Lemma is_path_neq0 (G : mgraph) (P : {set edge G}) : is_path P -> P != set0.
Proof. by case. Qed.

(** ** [is_matching] : witness + identity *)

Lemma is_matching_set0 (G : mgraph) : is_matching (@set0 (edge G)).
Proof. by move=> v; rewrite subdeg_set0. Qed.

(** ** [spanning_connected] / [spanning_tree] : witness *)

Lemma spanning_tree_unit : spanning_tree (G:=U) set0.
Proof.
split.
- by move=> x y; exists [::]; split; [case: x; case: y|].
- exact: acyclic_set0.
Qed.

(** ** [is_bridge] / [bridgeless] : witness *)

Lemma bridgeless_unit : bridgeless (U).
Proof. by case. Qed.

(** ** [cubic] : witness + identities *)

Lemma cubic_loopless (G : mgraph) : cubic G -> loopless G.
Proof. by case. Qed.

Lemma cubic_mdeg (G : mgraph) : cubic G -> forall v : G, mdeg v = 3.
Proof. by case. Qed.

(** Witness: two vertices joined by three parallel non-loop edges are cubic. *)
Lemma loopless_G3p : loopless G3p.
Proof. by case=> [[[[[]|[]]|]|]|]. Qed.

Lemma cubic_G3p : cubic G3p.
Proof. by split; [exact: loopless_G3p | exact: mdeg_G3p]. Qed.

(** ** [simple_mgraph] : witness *)

Lemma edges_at_unit (v : U) : edges_at v = set0.
Proof. by apply/setP => -[]. Qed.

Lemma simple_mgraph_unit : simple_mgraph (U).
Proof.
split; first by case.
move=> x y.
have ->: edges x y = set0 by apply/setP => -[].
by rewrite cards0.
Qed.

(** ** [eulerian] : witness + identity *)

Lemma mdeg_unit (v : U) : mdeg v = 0.
Proof. by rewrite /mdeg edges_at_unit cards0. Qed.

Lemma eulerian_unit : eulerian (U).
Proof. by split; [exact: mconnected_unit | move=> v; rewrite mdeg_unit]. Qed.

Lemma eulerian_mconnected (G : mgraph) : eulerian G -> mconnected G.
Proof. by case. Qed.

Lemma eulerian_Gd : eulerian Gd.
Proof.
split.
- by move=> x y; case: x => -[]; case: y => -[];
    [exists [::]|exists [:: Some None]|exists [:: None]|exists [::]].
- by move=> v; rewrite mdeg_Gd.
Qed.

(** ** [is_eulerian_tour] : witness *)

Lemma eulerian_tour_unit : is_eulerian_tour (G:=U) [::].
Proof. by split; [exists tt | case]. Qed.

(** ** [edge_partitionT] / [edge_partition_of] : witnesses + identities *)

Lemma edge_partitionT_Gd : edge_partitionT (G:=Gd) [:: [set: edge Gd]].
Proof. by move=> e; rewrite /= in_setT. Qed.

Lemma edge_partition_of_Gd :
  edge_partition_of (G:=Gd) [set: edge Gd] [:: [set: edge Gd]].
Proof. by move=> e; rewrite /= !in_setT. Qed.

Lemma edge_partition_of_unit :
  edge_partition_of (G:=U) set0 [::].
Proof. by case. Qed.

(** ** [cycle_decomposition_of] / [cycle_decomposition] / [path_decomposition] *)

Lemma cycle_decomposition_Gd : cycle_decomposition (G:=Gd) [:: [set: edge Gd]].
Proof.
split; last exact: edge_partitionT_Gd.
by move=> C; rewrite inE => /eqP ->; exact: is_circuit_Gd.
Qed.

Lemma cycle_decomposition_unit : cycle_decomposition (G:=U) [::].
Proof. by split; [move=> C | case]. Qed.

Lemma cycle_decomposition_of_Gd :
  cycle_decomposition_of (G:=Gd) [set: edge Gd] [:: [set: edge Gd]].
Proof.
split; last exact: edge_partition_of_Gd.
by move=> C; rewrite inE => /eqP ->; exact: is_circuit_Gd.
Qed.

Lemma path_decomposition_unit : path_decomposition (G:=U) [::].
Proof. by split; [move=> C | case]. Qed.

(** ** [cdc] : witness (digon double cover) + identity *)

Lemma cdc_Gd : cdc (G:=Gd) [:: [set: edge Gd]; [set: edge Gd]].
Proof.
split.
- by move=> C; rewrite !inE => /orP[] /eqP ->; exact: is_circuit_Gd.
- by move=> e; rewrite /= !in_setT.
Qed.

Lemma cdc_unit : cdc (G:=U) [::].
Proof. by split; [move=> C | case]. Qed.

(** ** [faithful_cover] : witness + identity (cdc is a faithful cover for [p=2]) *)

Lemma faithful_cover_Gd : faithful_cover (G:=Gd) (fun _ => 1) [:: [set: edge Gd]].
Proof.
split.
- by move=> C; rewrite inE => /eqP ->; exact: is_circuit_Gd.
- by move=> e; rewrite /= in_setT.
Qed.

Lemma cdc_faithful (G : mgraph) (L : seq {set edge G}) :
  cdc L -> faithful_cover (fun _ => 2) L.
Proof. by case=> ? H; split=> // e; exact: H. Qed.

(** ** [cut] : identities *)

Lemma cut_set0 (G : mgraph) : cut (@set0 G) = set0.
Proof. by apply/setP => e; rewrite !inE. Qed.

Lemma cut_setT (G : mgraph) : cut [set: G] = set0.
Proof. by apply/setP => e; rewrite !inE. Qed.

(** ** [admissible] : witness (the zero weighting) *)

Lemma admissible0 (G : mgraph) : admissible (G:=G) (fun _ => 0).
Proof.
move=> S e _; split; first by rewrite muln0.
by rewrite big1.
Qed.

(** ** [transition2_system] : witness (the digon's unique transition) *)

Lemma transition2_Gd :
  transition2_system (G:=Gd) (fun _ => [set [set: edge Gd]]).
Proof.
split.
- move=> v; rewrite edges_at_Gd; apply/and3P; split.
  + by rewrite /cover big_set1 eqxx.
  + exact: trivIset1.
  + by rewrite inE eq_sym -card_gt0 cardsT card_edge_Gd.
- by move=> v T; rewrite inE => /eqP ->; rewrite cardsT card_edge_Gd.
Qed.

(** ** [compatible_decomposition] : witness (vacuous, single vertex) *)

Lemma compatible_decomposition_unit :
  compatible_decomposition (G:=U) (fun _ => set0) [::].
Proof. by split; [exact: cycle_decomposition_unit | move=> C]. Qed.

(** ** [cyc_pairs] / [two_consecutive] : identities *)

Lemma cyc_pairs_nil (G : mgraph) : cyc_pairs (G:=G) [::] = [::].
Proof. by []. Qed.

Lemma two_consecutive_set0 (G : mgraph) (w : seq (edge G)) :
  two_consecutive w set0 = false.
Proof. by apply: negbTE; apply/hasPn => p _; rewrite in_set0. Qed.

(** ** [oddness_le] : witness (void graph, oddness 0) *)

Lemma oddness_le_void : oddness_le (V) 0.
Proof.
exists set0, [::]; split.
- by case.
- by split; [move=> C | case].
- by [].
Qed.
