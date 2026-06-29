(** * Topological.conjectures.grounding_D3cr — grounding lemmas for milestone D3cr.

    SIMPLE, Qed-closed sanity results validating the NEW primitive introduced in
    [D3cr.v] ([hypercube]) and certifying NON-VACUITY of the relational crossing
    invariant the four statements are built on.  For each new definition we record
    a SATISFIABLE witness and at least one textbook identity.  These are
    statement-validation lemmas, NOT the (open) conjectures themselves.

    New primitive covered:
      - [hypercube] (row 4, [@MOVE-to-base]): base case [hypercube 0 = 'K_1],
        the cartesian recurrence [hypercube d.+1 = 'K_2 □ hypercube d], and the
        textbook vertex-count identity [#|hypercube d| = 2 ^ d].

    Non-vacuity of the relational crossing invariant (addresses the review's
    vacuity concern on all four rows): [is_crossing_number] is genuinely INHABITED
    — [cr_K1], [cr_hypercube0], [cr_hypercube1] exhibit cr = 0 on planar carriers
    (Q_0 = K_1, Q_1 = K_2).  So the antecedent [is_crossing_number C v] is not
    silently empty.  (Non-ZERO inhabited instances, e.g. cr(K_5) = 1, additionally
    need the planarization UPPER bound — a drawing/geometry existence fact this
    combinatorial layer deliberately omits — so they are out of scope here; the
    LOWER bound cr(K_5) ≥ 1 is already grounded in [crossing] by
    [is_crossing_number_K5].)

    Helper [minor_card] (minor ⇒ #vertices non-increasing) and [small_wagner_planar]
    (≤ 4 vertices ⇒ Wagner-planar) are local, reusable, Qed-closed facts; they use
    only base / coq-graph-theory's [minor] API, no geometry and no axiom.

    The crossing primitives [is_crossing_number] / [crossing_planar_in] / [xsplit]
    are area-local foundations and are grounded in [crossing.v]
    ([crossing_number0], [wagner_planar_sub], [is_crossing_number_K5]); reused base
    primitives ([cartesian_product], [KB], ['K_n], [χ]) are NOT re-grounded. *)

From Topological Require Import foundations.crossing.
From Topological.conjectures Require Import D3cr.
From GraphTheory Require Import minor.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ============================================================================
    Reusable helpers: minor cardinality bound and small-graph planarity.
    ========================================================================== *)

(** A minor never has more vertices than its host: a minor model assigns each
    minor-vertex a NONEMPTY, pairwise-DISJOINT branch set, so a representative
    map [H -> G] is injective. *)
Lemma minor_card (G H : sgraph) : minor G H -> #|H| <= #|G|.
Proof.
case=> phi mm.
have [ne _ disj _] := minor_rmap_map mm.
set psi := (fun x : H => [set y | phi y == Some x]) in ne disj *.
case: (set_0Vmem [set: H]) => [HE|[x0 _]].
  by rewrite -cardsT HE cards0.
have [w0 _] : exists z : G, z \in psi x0 by apply/set0Pn; exact: ne x0.
pose g (x : H) : G := oapp idfun w0 [pick z in psi x].
have gP : forall x, g x \in psi x.
  move=> x; rewrite /g; case: pickP => [z zP|e]; first exact: zP.
  by case/set0Pn: (ne x) => z; rewrite (e z).
have ginj : injective g.
  move=> x y exy; apply/eqP; apply: contraT => xy.
  have D := disj x y xy.
  have : g y \in psi x :&: psi y by rewrite inE -{1}exy !gP.
  by rewrite (disjoint_setI0 D) inE.
exact: leq_card ginj.
Qed.

(** Every graph on at most 4 vertices is (Wagner-)planar: too small for a K5
    minor ([small_K_free]) or a K_{3,3} = [KB 3 3] minor (6 > 4 vertices, via
    [minor_card]). *)
Lemma small_wagner_planar (G : sgraph) : #|G| <= 4 -> wagner_planar G.
Proof.
move=> le4; split.
- exact: small_K_free le4.
- move=> H; have := leq_trans (minor_card H) le4.
  by rewrite card_sum !card_ord.
Qed.

(** ============================================================================
    [hypercube] — base case, cartesian recurrence, and vertex count.
    ========================================================================== *)

(** ** base case: Q_0 is the one-vertex graph K_1 (definitional). *)
Lemma hypercube_zero : hypercube 0 = 'K_1.
Proof. by []. Qed.

(** ** recurrence: Q_{d+1} is the box product K_2 □ Q_d (definitional). *)
Lemma hypercube_succ (d : nat) :
  hypercube d.+1 = cartesian_product 'K_2 (hypercube d).
Proof. by []. Qed.

(** ** textbook identity / witness: Q_d has exactly 2^d vertices. *)
Lemma hypercube_card (d : nat) : #|hypercube d| = 2 ^ d.
Proof.
elim: d => [|d IH] /=.
- by rewrite expn0 card_ord.
- by rewrite card_prod IH card_ord expnS.
Qed.

(** ============================================================================
    Non-vacuity: the relational crossing number is genuinely inhabited.
    ========================================================================== *)

(** ** witness: cr(K_1) = 0 (K_1 is planar). *)
Lemma cr_K1 : is_crossing_number 'K_1 0.
Proof. by apply/crossing_number0; apply: small_wagner_planar; rewrite card_ord. Qed.

(** ** witness: cr(Q_0) = 0 (Q_0 = K_1 is planar) — Row-4 antecedent inhabited. *)
Lemma cr_hypercube0 : is_crossing_number (hypercube 0) 0.
Proof. by apply/crossing_number0; apply: small_wagner_planar; rewrite hypercube_card. Qed.

(** ** witness: cr(Q_1) = 0 (Q_1 = K_2 is planar) — Row-4 antecedent inhabited. *)
Lemma cr_hypercube1 : is_crossing_number (hypercube 1) 0.
Proof. by apply/crossing_number0; apply: small_wagner_planar; rewrite hypercube_card. Qed.

(** ============================================================================
    Axiom-freeness audit: the four milestone-D3cr statements and the grounding
    lemmas are all closed under the global context (no Parameter/Axiom).
    ========================================================================== *)

Print Assumptions the_crossing_number_of_the_complete_bipartite_graph_statement.
Print Assumptions the_crossing_number_of_the_complete_graph_statement.
Print Assumptions crossing_numbers_and_coloring_statement.
Print Assumptions the_crossing_number_of_the_hypercube_statement.

Print Assumptions minor_card.
Print Assumptions small_wagner_planar.
Print Assumptions hypercube_card.
Print Assumptions cr_K1.
Print Assumptions cr_hypercube0.
Print Assumptions cr_hypercube1.
