(** * Chromatic.conjectures.grounding_U4 — grounding lemmas for milestone U4.

    SIMPLE, Qed-closed sanity results validating the new primitives introduced
    in [U4.v]: for each new definition we record a SATISFIABLE witness and at
    least one textbook identity.  These are statement-validation lemmas, not the
    (open/partial) conjectures themselves.

    Witness graphs are the small complete graphs ['K_0], ['K_1], ['K_n] and the
    one-vertex edgeless multigraph [unit_graph tt] (whose edge type is [void]),
    which make the degenerate/boundary cases of each primitive computable while
    still exercising the definitional content (proper colourings, choosability
    minimality, the paintability recursion, multigraph incidence/line/total
    constructions, complete-multipartite cardinality, acyclic colourings, and
    strong colourability).

    Planarity note: Row 10's statement primitive [acyclically_choosable] is
    validated here ([acyclic_colouring_complete], [acyclically_choosable_K1]);
    the planarity-gated STATEMENT itself ([acyclic_list_colouring_of_planar_
    graphs_statement]) is now genuinely faithful — its planarity hypothesis is
    base's combinatorial [wagner_planar] (no K5 / K3,3 minor, used opaquely), so
    no abstract placeholder remains.  Its colouring core is grounded via the
    [acyclically_choosable] witnesses above. *)

From GTBase Require Import base.
From GraphTheory Require Import minor mgraph.
From Chromatic.conjectures Require Import U4.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** [list_colourable] — witness: the identity colouring of ['K_n] from the
    full palette is a proper list-colouring (distinct vertices get distinct
    colours, which is exactly adjacency in a complete graph). *)
Lemma list_colourable_complete n :
  list_colourable (G := 'K_n) (fun _ : 'K_n => [set: 'K_n]).
Proof.
exists id; split.
- by move=> v; rewrite inE.
- by move=> x y; rewrite /edge_rel /=.
Qed.

(** ** [list_colourable_on] — degenerate identity: the empty induced subgraph
    is always (vacuously) L-colourable. *)
Lemma list_colourable_on_set0 n :
  list_colourable_on (G := 'K_n) (fun _ : 'K_n => [set: 'K_n]) set0.
Proof.
exists (fun=> None); split.
- by move=> v; rewrite in_set0.
- by move=> x y Hx _ _; rewrite in_set0 in Hx.
Qed.

(** ** [list_colourable_on] — witness on the full vertex set [setT]. *)
Lemma list_colourable_on_complete n :
  list_colourable_on (G := 'K_n) (fun _ : 'K_n => [set: 'K_n]) [set: 'K_n].
Proof.
exists (fun v => Some v); split.
- by move=> v _; exists v; rewrite inE.
- move=> x y _ _; rewrite /edge_rel /= => xy.
  by apply/eqP => -[] exy; rewrite exy eqxx in xy.
Qed.

(** ** [choosable] — witness: the one-vertex graph is 1-choosable. *)
Lemma choosable_K1 : choosable 'K_1 1.
Proof.
move=> C L HL.
have /card_gt0P[c Hc] : 0 < #|L ord0| by apply: leq_trans (HL ord0).
exists (fun _ => c); split.
- by move=> v; rewrite (ord1 v).
- by move=> x y xy; exfalso; move: xy;
     rewrite /edge_rel /= (ord1 x) (ord1 y) eqxx.
Qed.

(** ** [choosable] — boundary identity: no graph with a vertex is 0-choosable
    (empty lists cannot be respected); used for the minimality of [ch]. *)
Lemma not_choosable_K1_0 : ~ choosable 'K_1 0.
Proof.
move=> H.
have [f [Hf _]] := H bool (fun _ => set0) (fun _ => leq0n _).
by move: (Hf ord0); rewrite in_set0.
Qed.

(** ** [is_choice_number] — textbook identity: ch('K_1) = 1. *)
Lemma is_choice_number_K1 : is_choice_number 'K_1 1.
Proof.
split; first exact: choosable_K1.
move=> k Hk; case: k Hk => [|k] Hk //.
by case: (not_choosable_K1_0 Hk).
Qed.

(** ** [colourable_count] — identity: with full lists every vertex of ['K_n] is
    colourable, so λ_L = n = #|G|. *)
Lemma colourable_count_complete n :
  colourable_count (G := 'K_n) (fun _ : 'K_n => [set: 'K_n]) n.
Proof.
split.
- exists [set: 'K_n]; split; first exact: list_colourable_on_complete.
  by rewrite cardsT card_ord.
- move=> W _.
  by apply: leq_trans (max_card (mem W)) _; rewrite card_ord.
Qed.

(** ** [is_lambda] — witness/identity: λ_0('K_0) = 0 (no vertices, empty
    size-0 list assignment). *)
Lemma is_lambda_K0 : is_lambda 'K_0 0 0.
Proof.
split.
- exists bool, (fun _ : 'K_0 => set0); split; first by case.
  split.
  + exists set0; split; last by rewrite cards0.
    exists (fun=> None); split.
    * by move=> v Hv; rewrite in_set0 in Hv.
    * by move=> x y Hx _ _; rewrite in_set0 in Hx.
  + move=> W _.
    by apply: leq_trans (max_card (mem W)) _; rewrite card_ord.
- by move=> C L mu _ _.
Qed.

(** ** Paintability helpers. *)
Lemma setT_K0 : [set: 'K_0] = set0.
Proof. by apply/eqP; rewrite -cards_eq0 cardsT card_ord. Qed.

(** Once the alive set is empty, Painter has already won (any fuel). *)
Lemma paintableb_setT_empty (G : sgraph) n (f : G -> nat) :
  [set: G] = set0 -> paintableb n [set: G] f.
Proof. by move=> e; case: n => [|n] /=; rewrite e eqxx. Qed.

(** ** [paintable] — witness: the empty graph is paintable for any budget. *)
Lemma paintable_K0 (f : 'K_0 -> nat) : paintable f.
Proof. by apply: paintableb_setT_empty; exact: setT_K0. Qed.

(** ** [k_paintable] — witness: ['K_0] is k-paintable for every k. *)
Lemma k_paintable_K0 k : k_paintable 'K_0 k.
Proof. exact: paintable_K0. Qed.

(** ** [is_online_choice_number] — textbook identity: ch^OL('K_0) = 0. *)
Lemma is_online_choice_number_K0 : is_online_choice_number 'K_0 0.
Proof. by split; [exact: k_paintable_K0 | move=> k _]. Qed.

(** ** [loopless] — witness: the one-vertex edgeless multigraph is loopless
    (its edge type is empty). *)
Lemma loopless_unit : loopless (unit_graph tt).
Proof. by case. Qed.

(** ** [mDelta] — identity: the edgeless multigraph has maximum degree 0. *)
Lemma mDelta_unit : mDelta (unit_graph tt) = 0.
Proof. by rewrite /mDelta; apply: big1 => v _; apply: eq_card0; case. Qed.

(** ** [Delta_edge_critical] — witness: vacuously Δ-edge-critical (its line
    graph has no vertices). *)
Lemma Delta_edge_critical_unit : Delta_edge_critical (unit_graph tt).
Proof. by case. Qed.

(** ** [line_graph] — identity: the line graph of an edgeless multigraph is
    empty. *)
Lemma line_graph_unit_empty : #|line_graph (unit_graph tt)| = 0.
Proof. exact: card_void. Qed.

(** ** [total_graph] — identity: the total graph of the edgeless one-vertex
    multigraph has no edges. *)
Lemma total_graph_unit_edgeless (a b : total_graph (unit_graph tt)) :
  ~~ (a -- b).
Proof. by case: a => [[]|[]]; case: b => [[]|[]]; rewrite /edge_rel /=. Qed.

(** ** [madj] — textbook identity: no vertex is multi-adjacent to itself. *)
Lemma madj_irrefl (G : mgraph) (x : G) : ~~ madj x x.
Proof. by rewrite /madj eqxx. Qed.

(** ** [share_endpoint] / [incident] — identity: every edge shares an endpoint
    with itself (it is incident to its own source). *)
Lemma share_endpoint_refl (G : mgraph) (e : edge G) : share_endpoint e e.
Proof.
apply/existsP; exists (endpoint false e); apply/andP; split;
  by apply/existsP; exists false; rewrite eqxx.
Qed.

(** ** [line_rel] — identity: adjacency in the line graph entails sharing an
    endpoint. *)
Lemma line_rel_share (G : mgraph) (e1 e2 : edge G) :
  line_rel e1 e2 -> share_endpoint e1 e2.
Proof. by move=> /andP[_]. Qed.

(** ** [total_rel] — identity: in the total graph a vertex is adjacent to every
    edge it is the source of. *)
Lemma total_vertex_edge (G : mgraph) (e : edge G) :
  (inl (source e) : total_graph G) -- (inr e).
Proof. by rewrite /edge_rel /=; apply/existsP; exists false; rewrite eqxx. Qed.

(** ** [complete_multipartite] — textbook identity: K_{m*k} has exactly m·k
    vertices. *)
Lemma card_complete_multipartite k m :
  #|complete_multipartite k m| = k * m.
Proof. by rewrite card_prod !card_ord. Qed.

(** ** [cmp_rel] — identity: vertices in the same part are non-adjacent. *)
Lemma cmp_same_part k m (i : 'I_k) (a b : 'I_m) :
  ~~ @edge_rel (complete_multipartite k m) (i, a) (i, b).
Proof. by rewrite /edge_rel /= /cmp_rel /= eqxx. Qed.

(** ** [cmp_rel] — identity: vertices in different parts are adjacent. *)
Lemma cmp_diff_part k m (i j : 'I_k) (a b : 'I_m) :
  i != j -> @edge_rel (complete_multipartite k m) (i, a) (j, b).
Proof. by move=> hij; rewrite /edge_rel /=. Qed.

(** ** [acyclic_colouring] — witness: the identity colouring of ['K_n] is
    acyclic (all colours distinct, so every cycle is rainbow). *)
Lemma acyclic_colouring_complete n :
  acyclic_colouring (G := 'K_n) (fun _ : 'K_n => [set: 'K_n]) id.
Proof.
split.
- by move=> v; rewrite inE.
- by move=> x y; rewrite /edge_rel /=.
- move=> c /andP[_ uc] hsz.
  by rewrite map_id (undup_id uc).
Qed.

(** ** [acyclically_choosable] — witness: ['K_1] is acyclically 1-choosable
    (no edges, no genuine cycles). *)
Lemma acyclically_choosable_K1 : acyclically_choosable 'K_1 1.
Proof.
move=> C L HL.
have /card_gt0P[c Hc] : 0 < #|L ord0| by apply: leq_trans (HL ord0).
exists (fun _ => c); split.
- by move=> v; rewrite (ord1 v).
- by move=> x y xy; exfalso; move: xy;
     rewrite /edge_rel /= (ord1 x) (ord1 y) eqxx.
- move=> co /andP[_ /card_uniqP eqsz] hsz.
  move: (max_card (mem co)); rewrite eqsz card_ord => h1.
  move: (leqW h1) => h2.
  by move: hsz; rewrite ltnNge h2.
Qed.

(** ** [strongly_colorable] — witness: the one-vertex graph is strongly
    1-colourable. *)
Lemma strongly_colorable_K1 : strongly_colorable 'K_1 1.
Proof.
move=> P _ _.
exists (fun _ => ord0); split.
- by move=> x y xy; exfalso; move: xy;
     rewrite /edge_rel /= (ord1 x) (ord1 y) eqxx.
- by move=> B _ x y _ _ _; rewrite (ord1 x) (ord1 y).
Qed.
