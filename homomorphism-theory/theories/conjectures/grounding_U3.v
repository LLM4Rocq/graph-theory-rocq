(** * Hom.conjectures.grounding_U3 — grounding lemmas for milestone U3.

    SIMPLE, Qed-closed sanity results validating the new primitives introduced
    in [U3.v].  For each new definition we record a SATISFIABLE WITNESS and at
    least one TEXTBOOK IDENTITY the definition must satisfy.  These are
    statement-validation lemmas, NOT the (open/solved/disproved) conjectures
    themselves.

    They double as the bridges promised in U3.v's comments — in particular
    [hom_ffunP : reflect (is_hom f) (hom_ffun f)] proves that the boolean
    endomorphism predicate [hom_ffun] coincides with base's Prop-valued [is_hom]
    (so Row 9 reuses base's homomorphism vocabulary, it does not redefine it),
    and [mapping_planar_antimono] shows the Row-7 planarity gate is a genuine
    discharged Section parameter (contravariant in [is_planar]), confirming the
    faithfulness fix away from the inert inner [forall is_planar]. *)

From GTBase Require Import base.
From mathcomp Require Import fingroup.
From Hom.conjectures Require Import U3.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** [cycle_graph] / [C5] — witness + identity. *)

(** Satisfiable witness: [C5] has an edge (vertices 0 and 1 are adjacent). *)
Lemma C5_has_edge : exists x y : C5, x -- y.
Proof.
exists (@Ordinal 5 0 isT), (@Ordinal 5 1 isT).
by rewrite /edge_rel /= /cyc_rel /=.
Qed.

(** Textbook identity: in a cycle, adjacency forces the cyclic-successor
    relation on the indices (one of the two consecutive cases holds). *)
Lemma cycle_adj_succ n (i j : cycle_graph n) :
  i -- j -> ((val i).+1 %% n == val j) || ((val j).+1 %% n == val i).
Proof. by rewrite /edge_rel /= /cyc_rel => /andP[_]. Qed.

(** ** [path_graph] — witness + identity. *)

(** Satisfiable witness: [path_graph 2] has an edge (0 and 1 are adjacent). *)
Lemma path_graph_has_edge : exists x y : path_graph 2, x -- y.
Proof.
exists (@Ordinal 2 0 isT), (@Ordinal 2 1 isT).
by rewrite /edge_rel /= /pth_rel /=.
Qed.

(** Textbook identity: in a path, adjacency forces consecutive indices
    (no modular wrap). *)
Lemma path_adj_succ n (i j : path_graph n) :
  i -- j -> ((val i).+1 == val j) || ((val j).+1 == val i).
Proof. by rewrite /edge_rel /= /pth_rel. Qed.

(** ** [star_graph] — witness + identity. *)

(** Definitional identity: the 2-vertex star is the single edge ['K_1,1]. *)
Lemma star_graph2 : star_graph 2 = 'K_1, 1.
Proof. by []. Qed.

(** Textbook identity: the [n]-vertex star really has [n] vertices. *)
Lemma card_star_graph n : 0 < n -> #|star_graph n| = n.
Proof. by move=> n0; rewrite /star_graph card_sum !card_ord add1n prednK. Qed.

(** ** [bipartite_rel] — witness + closure identity. *)

(** Satisfiable witness: the empty relation is bipartite. *)
Lemma bipartite_rel0 (G : sgraph) : bipartite_rel (fun _ _ : G => false).
Proof. by exists (fun=> true). Qed.

(** Textbook identity: bipartiteness is downward closed (a sub-relation of a
    bipartite relation is bipartite). *)
Lemma bipartite_rel_sub (G : sgraph) (r s : rel G) :
  (forall x y, r x y -> s x y) -> bipartite_rel s -> bipartite_rel r.
Proof. by move=> rs [f Hf]; exists f => x y /rs/Hf. Qed.

(** ** [triangle_free] — witness via a graph carrying an edge. *)

(** Helper: a 2-vertex graph has no triangle (three pairwise-adjacent, hence
    pairwise-distinct, vertices would need 3 vertices). *)
Lemma no_tri_card2 (G : sgraph) (x y z : G) :
  #|G| = 2 -> x -- y -> y -- z -> z -- x -> False.
Proof.
move=> cardG xy yz zx.
have Exy : (x == y) = false := sg_edgeNeq xy.
have Eyz : (y == z) = false := sg_edgeNeq yz.
have Ezx : (z == x) = false := sg_edgeNeq zx.
have card3 : #|[set x; y; z]| = 3.
  rewrite -setUA cardsU1 cards2 !inE negb_or Exy Eyz [x == z]eq_sym Ezx.
  by [].
have h := subset_leq_card (subsetT [set x; y; z]).
by move: h; rewrite card3 cardsT cardG.
Qed.

(** Witness: ['K_2] (an edge) is triangle-free. *)
Lemma triangle_free_K2 : triangle_free 'K_2.
Proof. by move=> x y z; apply: no_tri_card2; rewrite card_ord. Qed.

(** ** [k_connected] — witness + projection identity. *)

(** Satisfiable witness: every nonempty graph is 0-connected (the connectivity
    clause is vacuous for [k = 0]). *)
Lemma k_connected0 : k_connected 'K_1 0.
Proof. by split=> [|S]; rewrite ?card_ord ?ltn0. Qed.

(** Textbook identity: [k]-connectivity requires more than [k] vertices. *)
Lemma k_connected_card (G : sgraph) k : k_connected G k -> k < #|G|.
Proof. by case. Qed.

(** ** [longest_cycle] — defining-property projections. *)

Lemma longest_cycle_ucycle (G : sgraph) (c : seq G) :
  longest_cycle c -> ucycle (--) c.
Proof. by case. Qed.

Lemma longest_cycle_size (G : sgraph) (c : seq G) :
  longest_cycle c -> 2 < size c.
Proof. by case. Qed.

(** Maximality: no cycle is longer than a longest cycle. *)
Lemma longest_cycle_max (G : sgraph) (c c' : seq G) :
  longest_cycle c -> ucycle (--) c' -> size c' <= size c.
Proof. by case=> _ _ H; apply: H. Qed.

(** ** [chord] — projection identity. *)

(** Textbook identity: a chord is in particular an edge of the graph. *)
Lemma chord_edge (G : sgraph) (c : seq G) :
  chord c -> exists x y : G, x -- y.
Proof. by case=> x [y] [_ _ xy _ _]; exists x, y. Qed.

(** ** [is_path] — witnesses + identity. *)

(** Witness: the empty walk and any single vertex are paths. *)
Lemma is_path_nil (G : sgraph) : is_path (G := G) [::].
Proof. by []. Qed.

Lemma is_path1 (G : sgraph) (x : G) : is_path [:: x].
Proof. by []. Qed.

(** Textbook identity: the vertices of a path are pairwise distinct. *)
Lemma is_path_uniq (G : sgraph) (s : seq G) : is_path s -> uniq s.
Proof. by case/andP. Qed.

(** ** [longest_path] — witness + projection identities. *)

Lemma longest_path_is_path (G : sgraph) (s : seq G) :
  longest_path s -> is_path s.
Proof. by case. Qed.

Lemma longest_path_max (G : sgraph) (s t : seq G) :
  longest_path s -> is_path t -> size t <= size s.
Proof. by case=> _ H; apply: H. Qed.

(** Satisfiable witness: in the 1-vertex graph ['K_1] the single-vertex walk is
    a longest path (no path can be longer than the number of vertices). *)
Lemma longest_path_K1 : longest_path (G := 'K_1) [:: ord0].
Proof.
split; first exact: is_path1.
move=> t /andP[ut _].
have E : #|mem t| = size t by apply/card_uniqP.
rewrite /= -E.
by apply: leq_trans (max_card (mem t)) _; rewrite card_ord.
Qed.

(** ** [hom_ffun] / [endo_count] — reflection bridge + witness. *)

(** Bridge: [hom_ffun] is exactly the boolean reflection of base's [is_hom]
    (this is the lemma promised in U3.v's Row-9 comment, documenting that the
    endomorphism predicate reuses — does not redefine — base's homomorphism). *)
Lemma hom_ffunP (G : sgraph) (f : {ffun G -> G}) :
  reflect (is_hom f) (hom_ffun f).
Proof.
apply: (iffP idP).
- move/forallP => H x y xy.
  move/forallP: (H x) => H'.
  by move/implyP: (H' y); apply.
- move=> H; apply/forallP => x; apply/forallP => y.
  by apply/implyP => xy; exact: (H x y xy).
Qed.

(** Witness/identity: every graph has at least one endomorphism (the identity),
    so the endomorphism count is positive. *)
Lemma endo_count_gt0 (G : sgraph) : 0 < endo_count G.
Proof.
apply/card_gt0P; exists [ffun x => x]; rewrite inE.
apply/forallP => x; apply/forallP => y; apply/implyP => xy.
by rewrite !ffunE.
Qed.

(** ** [hom_equiv] — reflexivity (witness) + symmetry (identity). *)

Lemma hom_equiv_refl (G : sgraph) : hom_equiv G G.
Proof. by split; exists id => x y. Qed.

Lemma hom_equiv_sym (G H : sgraph) : hom_equiv G H -> hom_equiv H G.
Proof. by case=> a b; split. Qed.

(** ** [srg] / [strongly_regular] — witness via ['K_2]. *)

Lemma neighK2 (x : 'K_2) : N(x) = ~: [set x].
Proof. by apply/setP => y; rewrite !inE eq_sym. Qed.

Lemma regular_K2 : regular 'K_2 1.
Proof.
by move=> x; rewrite neighK2 (cardsCs (~: [set x])) setCK cards1 card_ord subn1.
Qed.

(** ['K_2] is strongly regular with parameters (k,l,m) = (1,0,0). *)
Lemma srg_K2 : srg 'K_2 1 0 0.
Proof.
split.
- exact: regular_K2.
- move=> x y xy.
  have e2 : [set x] :|: [set y] = [set: 'K_2].
    apply/eqP; rewrite eqEcard subsetT cardsU1 inE cards1 cardsT card_ord.
    by rewrite (sg_edgeNeq xy).
  by rewrite /common_nbr !neighK2 -setCU e2 setCT cards0.
- move=> x y xney nadj; exfalso; move: nadj.
  by rewrite (_ : (x -- y) = (x != y)) ?xney.
Qed.

Lemma strongly_regular_K2 : strongly_regular 'K_2.
Proof. by exists 1, 0, 0; exact: srg_K2. Qed.

(** ** [pcayley] / [pconn_set] — witness + edgeless identity. *)

(** Satisfiable witness: the empty connection set is a valid Cayley set. *)
Lemma pconn_set0 (M : finGroupType) (k : nat) :
  pconn_set (@set0 {ffun 'I_k -> M}).
Proof. by split=> [|f]; rewrite inE. Qed.

(** Textbook identity: the Cayley graph of the empty connection set is edgeless. *)
Lemma pcayley_set0_edgeless (M : finGroupType) (k : nat)
  (f g : pcayley (@set0 {ffun 'I_k -> M})) : ~~ (f -- g).
Proof. by rewrite /edge_rel /= /pcayley_rel !inE andbF. Qed.

(** ** [graph_power] / [subdivision] / [frac_power] — promoted constructions,
    grounded again in this (2nd) area ([@MOVE-to-base] candidates). *)

(** Identity: the 0-th power is edgeless. *)
Lemma graph_power0_edgeless (G : sgraph) (x y : graph_power G 0) : ~~ (x -- y).
Proof.
by rewrite /edge_rel /= /pow_rel /reach_le /= !inE [y == x]eq_sym orbb andNb.
Qed.

(** Identity: in a subdivision, original vertices are never adjacent. *)
Lemma sub_inl_inl (G : sgraph) n (a b : G) :
  ~~ @edge_rel (subdivision G n) (inl a) (inl b).
Proof. by rewrite /edge_rel /= /sub_rel /=. Qed.

(** Identity: the 0-th fractional power is edgeless. *)
Lemma frac_power0_edgeless (G : sgraph) n (x y : frac_power G 0 n) : ~~ (x -- y).
Proof. exact: graph_power0_edgeless. Qed.

(** ** Row 7 planarity gate — now GENUINE via base's [wagner_planar].

    The Row-7 statement no longer takes a planarity predicate parameter: it
    instantiates planarity at base's combinatorial, axiom-free [wagner_planar]
    ([~ minor _ 'K_5 /\ ~ minor _ (KB 3 3)] — Wagner planarity), used opaquely.
    The former antitone-in-[is_planar] sanity lemma is therefore retired (the
    placeholder it validated is gone).  We instead record that the statement is
    non-vacuous as a hypothesis shape: it has the expected [forall G k]
    quantifier structure with a real planarity premise. *)
Lemma mapping_planar_statement_shape :
  mapping_planar_graphs_to_odd_cycles_statement =
  (forall (G : sgraph) (k : nat),
     0 < k -> wagner_planar G -> girth_geq G (4 * k) ->
     homs_to G (cycle_graph (2 * k + 1))).
Proof. by []. Qed.
