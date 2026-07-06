(** * Chromatic.conjectures.grounding_U8 — grounding lemmas for milestone U8.

    SIMPLE, Qed-closed sanity results validating the NEW primitives introduced
    in [U8.v] (χ-boundedness / vertex-minor vocabulary).  For each new
    definition we record a SATISFIABLE witness and at least one textbook
    identity.  These are statement-validation lemmas, NOT the (open) conjectures
    themselves.

    New primitives covered:
      - [chi_bounded]      : empty-class witness + hereditary (subclass) identity.
      - [has_induced]      : reflexivity (every graph contains itself as an
                             induced subgraph on the full vertex set).
      - [local_complement] : vertex set unchanged; adjacency law; edges incident
                             to [v] preserved; adjacency among distinct common
                             neighbours of [v] toggled.
      - [vminorR]/[vertex_minor] : reflexivity; a local complement and a vertex
                             deletion are both vertex-minors.
      - [vminor_closed]    : the class of all graphs is closed; a closed class
                             containing [G] contains all of [G]'s local
                             complements.
      - [proper_class]     : the empty class is proper; the class of all graphs
                             is NOT proper.
      - joint non-vacuity : the empty class simultaneously satisfies BOTH Row-3
                             hypotheses ([vminor_closed] and [proper_class]). *)

From GTBase Require Import base.
From Chromatic.conjectures Require Import U8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ============================================================================
    [chi_bounded] — χ-boundedness of a graph class.
    ========================================================================== *)

(** ** witness: the empty class is χ-bounded (any bounding function works). *)
Lemma chi_bounded_empty : chi_bounded (fun _ : sgraph => False).
Proof. by exists (fun _ => 0) => G []. Qed.

(** ** textbook identity: χ-boundedness is hereditary — a subclass of a
    χ-bounded class is χ-bounded (same bounding function). *)
Lemma chi_bounded_sub (F F' : sgraph -> Prop) :
  (forall G, F G -> F' G) -> chi_bounded F' -> chi_bounded F.
Proof. by move=> sub [f Hf]; exists f => G FG; apply: Hf; apply: sub. Qed.

(** ============================================================================
    [has_induced] — T occurs as an induced subgraph of G.
    ========================================================================== *)

(** Helper: a graph is isomorphic to its own induced subgraph on the full
    vertex set ([val] is the witnessing bijection). *)
Lemma induced_setT_diso (G : sgraph) : induced [set: G] ≃ G.
Proof.
apply: (@Diso'' (induced [set: G]) G val (fun x => Sub x (in_setT x))).
- by move=> x; apply: val_inj.
- by move=> x; rewrite SubK.
- by move=> x y.
- by move=> x y.
Qed.

(** ** witness + textbook identity: [has_induced] is reflexive — every graph
    contains itself as an induced subgraph (on the full vertex set). *)
Lemma has_induced_refl (G : sgraph) : has_induced G G.
Proof. by exists [set: G]; constructor; apply: diso_sym; apply: induced_setT_diso. Qed.

(** ============================================================================
    [local_complement] — local complementation at a vertex.
    ========================================================================== *)

(** ** identity: local complementation does not change the vertex set. *)
Lemma card_local_complement (G : sgraph) (v : G) :
  #|local_complement v| = #|G|.
Proof. by []. Qed.

(** ** textbook identity: the defining adjacency law of [local_complement]. *)
Lemma local_complement_adjE (G : sgraph) (v : G) (x y : G) :
  ((x : local_complement v) -- (y : local_complement v))
    = (x != y) && ((x -- y) (+) ((x -- v) && (y -- v))).
Proof. by []. Qed.

(** ** textbook identity: edges incident to [v] are preserved by local
    complementation at [v]. *)
Lemma local_complement_at_v (G : sgraph) (v : G) (x : G) :
  ((x : local_complement v) -- (v : local_complement v)) = (x -- v).
Proof.
rewrite local_complement_adjE (sg_irrefl v) andbF addbF.
case E: (x -- v); rewrite ?andbF // andbT.
by rewrite (sg_edgeNeq E).
Qed.

(** ** textbook identity: adjacency between two DISTINCT common neighbours of
    [v] is toggled by local complementation at [v]. *)
Lemma local_complement_toggle (G : sgraph) (v : G) (x y : G) :
  x != y -> x -- v -> y -- v ->
  ((x : local_complement v) -- (y : local_complement v)) = ~~ (x -- y).
Proof. by move=> xy xv yv; rewrite local_complement_adjE xy xv yv /= addbT. Qed.

(** ============================================================================
    [vminorR] / [vertex_minor] — the vertex-minor relation.
    ========================================================================== *)

(** ** witness + identity: every graph is a vertex-minor of itself. *)
Lemma vertex_minor_refl (G : sgraph) : vertex_minor G G.
Proof. exact: vminorR_refl. Qed.

(** ** textbook identity: a local complement is a vertex-minor. *)
Lemma vertex_minor_lc (G : sgraph) (v : G) :
  vertex_minor (local_complement v) G.
Proof. apply: (@vminorR_lc G G _ v); [exact: vminorR_refl | exact: diso_id]. Qed.

(** ** textbook identity: a single vertex deletion yields a vertex-minor. *)
Lemma vertex_minor_del (G : sgraph) (v : G) :
  vertex_minor (induced [set u : G | u != v]) G.
Proof. apply: (@vminorR_del G G _ v); [exact: vminorR_refl | exact: diso_id]. Qed.

(** ============================================================================
    [vminor_closed] — closure under taking vertex-minors.
    ========================================================================== *)

(** ** witness: the class of ALL graphs is vertex-minor-closed. *)
Lemma vminor_closed_all : vminor_closed (fun _ : sgraph => True).
Proof. by []. Qed.

(** ** textbook identity: a vertex-minor-closed class containing [G] contains
    every local complement of [G]. *)
Lemma vminor_closed_lc (F : sgraph -> Prop) (G : sgraph) (v : G) :
  vminor_closed F -> F G -> F (local_complement v).
Proof. by move=> cl FG; apply: (cl G) => //; apply: vertex_minor_lc. Qed.

(** ============================================================================
    [proper_class] — a class omitting some graph.
    ========================================================================== *)

(** ** witness: the empty class is proper (it omits [K_1], indeed everything). *)
Lemma proper_class_empty : proper_class (fun _ : sgraph => False).
Proof. by exists 'K_1; case. Qed.

(** ** textbook identity: the class of all graphs is NOT proper. *)
Lemma not_proper_class_all : ~ proper_class (fun _ : sgraph => True).
Proof. by case=> G; apply. Qed.

(** ============================================================================
    Joint non-vacuity of Row 3's hypotheses.
    The empty class simultaneously satisfies [vminor_closed] and [proper_class],
    so the universally quantified Row-3 statement is not over an empty domain. *)
Lemma row3_hypotheses_satisfiable :
  vminor_closed (fun _ : sgraph => False) /\ proper_class (fun _ : sgraph => False).
Proof. by split; [move=> G H [] | exact: proper_class_empty]. Qed.

(** ============================================================================
    Axiom-freeness audit for the three milestone-U8 statements.
    ========================================================================== *)

Print Assumptions bounding_the_chromatic_number_of_triangle_free_graph_statement.
Print Assumptions graphs_with_a_forbidden_induced_tree_are_chi_bounded_statement.
Print Assumptions vertex_minor_closed_classes_are_chi_bounded_statement.

(** ============================================================================
    Row 1 — triangle-free guard (inlined in
    [bounding_the_chromatic_number_of_triangle_free_graph_statement]).
    ========================================================================== *)

(** ** inhabitation: 'K_2 (a graph WITH an edge) is triangle-free.  Three
    pairwise-adjacent vertices would be pairwise distinct, but 'K_2 has only 2
    vertices, so no triangle exists. *)
Lemma triangle_free_K2 (x y z : 'K_2) : x -- y -> y -- z -> z -- x -> False.
Proof.
by move: x y z => -[[|[|?]] ?] [[|[|?]] ?] [[|[|?]] ?]; rewrite /edge_rel //=.
Qed.

(** ** guard-has-teeth: 'K_3 is NOT triangle-free — the three distinct vertices
    0,1,2 are pairwise adjacent, forming a triangle.  Rules out an accidentally
    vacuous guard that would apply the bound to every graph. *)
Lemma not_triangle_free_K3 :
  ~ (forall x y z : ('K_3), x -- y -> y -- z -> z -- x -> False).
Proof.
move=> H.
by apply: (H (@Ordinal 3 0 isT) (@Ordinal 3 1 isT) (@Ordinal 3 2 isT));
   rewrite /edge_rel /=.
Qed.

(** ============================================================================
    TECHNIQUE #3 — independent re-encoding of [triangle_free] and a proved [<->].

    [triangle_free] is a LOCAL statement: no three vertices are pairwise
    adjacent.  The independent second encoding is the GLOBAL girth condition
    [girth_geq G 4] (from base): every genuine [ucycle] (size > 2) has length
    ≥ 4 — i.e. there is no 3-cycle, stated over ALL edge-sequences that are
    unordered cycles rather than over triples of vertices.

    The two are structurally unrelated (three-vertex local triple vs universal
    over [ucycle]s = [cycle && uniq] closed walks), and the equivalence is NOT
    definitional: the forward direction case-splits on [size c] and unfolds
    [cycle]/[path]/[rcons] on a 3-element list to expose the three triangle
    edges; the backward direction builds the explicit 3-cycle [[x; y; z]],
    discharging [cycle] from the three edges and [uniq] from pairwise
    distinctness (via [sg_edgeNeq]).  A dropped edge or a wrong threshold would
    break the [<->]. *)
Lemma triangle_free_girth (G : sgraph) : triangle_free G <-> girth_geq G 4.
Proof.
split.
- (* local no-triangle  ⇒  every genuine cycle has length ≥ 4 *)
  move=> tf c uc sz.
  case: c uc sz => [|a [|b [|c' [|d l]]]] //= uc sz.
  (* the only non-immediate branch is [c = [:: a; b; c']] (size 3) *)
  exfalso.
  move: uc => /andP[Hc _].
  move: Hc => /=; rewrite andbT => /andP[Hab /andP[Hbc Hca]].
  exact: (tf a b c' Hab Hbc Hca).
- (* girth ≥ 4  ⇒  no triangle: a triangle would be a genuine 3-cycle *)
  move=> gg x y z xy yz zx.
  have xny : x != y by rewrite (sg_edgeNeq xy).
  have ynz : y != z by rewrite (sg_edgeNeq yz).
  have znx : z != x by rewrite (sg_edgeNeq zx).
  have xnz : x != z by rewrite eq_sym.
  have Huc : ucycle (--) [:: x; y; z].
    rewrite /ucycle /= xy yz zx /= !negb_or.
    by rewrite xny xnz ynz.
  by move: (gg [:: x; y; z] Huc isT).
Qed.
