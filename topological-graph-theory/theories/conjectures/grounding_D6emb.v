(** * Topological.conjectures.grounding_D6emb — grounding lemmas for milestone D6emb.

    SIMPLE, Qed-closed sanity results validating the NEW area-specific primitives
    introduced in [D6emb.v] — the [antiprism] graph construction (with its
    directed/symmetrised adjacencies [anti_dir]/[anti_rel]) and the classification
    predicates [is_prism] / [is_antiprism].  For each new definition we record a
    SATISFIABLE witness and at least one textbook identity.  These are
    statement-validation lemmas, NOT the (open) conjectures themselves.

    New primitives covered:
      - [antiprism] / [anti_dir] / [anti_rel]:
          * textbook identity [antiprism_card]: the n-antiprism has exactly [2*n]
            vertices (two n-gons);
          * satisfiable witnesses [anti_dir_rung] / [anti_rel_rung]: the vertical
            rung [(i,true) ~ (i,false)] is a genuine (directed and symmetric) edge,
            so the adjacency relation is non-empty — [antiprism n] is not the empty
            graph for [n > 0].
      - [is_prism]:
          * satisfiable witness [is_prism_C3]: [C_3 □ K_2] IS a prism (the class is
            inhabited, so the [~ is_prism] hypothesis of Row 3 is a real constraint);
          * textbook identity [is_prism_iso]: "being a prism" is an isomorphism
            invariant (closed under [≃], as it must be — the class is defined up to
            [diso]).
      - [is_antiprism]:
          * satisfiable witness [is_antiprism_3]: [antiprism 3] IS an antiprism;
          * textbook identity [is_antiprism_iso]: isomorphism invariance.

    All reused cross-area primitives ([cartesian_product], [cycle_graph], ['K_2],
    [cyc_rel], [≃]/[diso_id]/[diso_comp]) come from GTBase.base / coq-graph-theory
    and are NOT re-grounded here.  Embedding-side non-vacuity ([inhabited
    (embedding G)] for every [G]) is already proven in the foundation
    ([embedding.embedding_exists]) and is likewise not re-grounded. *)

From GTBase Require Import base.
From mathcomp Require Import fingroup perm.
From Topological.foundations Require Import embedding.
From Topological.conjectures Require Import D6emb.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ============================================================================
    [antiprism] / [anti_dir] / [anti_rel] — vertex count and edge witnesses.
    ========================================================================== *)

(** ** textbook identity: the n-antiprism has [2*n] vertices (two n-gons). *)
Lemma antiprism_card (n : nat) : #|antiprism n| = n * 2.
Proof. by rewrite card_prod card_ord card_bool. Qed.

(** ** witness: the vertical rung [top i -> bottom i] is a directed edge. *)
Lemma anti_dir_rung (n : nat) (i : 'I_n) : anti_dir (i, true) (i, false).
Proof. by rewrite /anti_dir /= eqxx. Qed.

(** ** witness: hence [(i,true) ~ (i,false)] is a genuine (symmetric) edge, so the
    antiprism's adjacency is non-empty — [antiprism n] is not the empty graph. *)
Lemma anti_rel_rung (n : nat) (i : 'I_n) : anti_rel (i, true) (i, false).
Proof. by rewrite /anti_rel /anti_dir /= eqxx. Qed.

(** ============================================================================
    [is_prism] — the class is inhabited, and is an isomorphism invariant.
    ========================================================================== *)

(** ** witness: [C_3 □ K_2] is a prism (so [~ is_prism] is a real constraint). *)
Lemma is_prism_C3 : is_prism (cartesian_product (cycle_graph 3) 'K_2).
Proof. by exists 3; split => //; exact: (inhabits diso_id). Qed.

(** ** textbook identity: "being a prism" is closed under graph isomorphism. *)
Lemma is_prism_iso (G H : sgraph) : G ≃ H -> is_prism H -> is_prism G.
Proof.
by move=> iso [m [Hm [J]]]; exists m; split => //; exact: (inhabits (diso_comp iso J)).
Qed.

(** ============================================================================
    [is_antiprism] — the class is inhabited, and is an isomorphism invariant.
    ========================================================================== *)

(** ** witness: [antiprism 3] is an antiprism. *)
Lemma is_antiprism_3 : is_antiprism (antiprism 3).
Proof. by exists 3; split => //; exact: (inhabits diso_id). Qed.

(** ** textbook identity: "being an antiprism" is closed under graph isomorphism. *)
Lemma is_antiprism_iso (G H : sgraph) : G ≃ H -> is_antiprism H -> is_antiprism G.
Proof.
by move=> iso [m [Hm [J]]]; exists m; split => //; exact: (inhabits (diso_comp iso J)).
Qed.

(** ============================================================================
    Axiom-freeness audit: the three milestone-D6emb statements and every
    grounding lemma are closed under the global context (no Parameter/Axiom).
    ========================================================================== *)

Print Assumptions grunbaums_statement.
Print Assumptions the_circular_embedding_statement.
Print Assumptions what_is_the_largest_graph_of_positive_curvature_statement.

Print Assumptions antiprism_card.
Print Assumptions anti_dir_rung.
Print Assumptions anti_rel_rung.
Print Assumptions is_prism_C3.
Print Assumptions is_prism_iso.
Print Assumptions is_antiprism_3.
Print Assumptions is_antiprism_iso.
