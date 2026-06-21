(** * Digraph.conjectures.grounding_pathfas_tww — grounding path-FAS + ordered twin-width

    Solo grounding pass (the round-3 agent for this cluster stalled on transient API
    rate-limiting before writing a file).  Pass-1 [grounding_fas_unvd.v] already grounds the
    TRANSITIVE case (Δ*(TTₙ) = 0, has_LFO(TTₙ), linear_forest of the edgeless graph), so
    here we ground the structural/relational facts the path-FAS and ordered-twin-width
    definitions must satisfy:
      - the length-3 / length-4 directed-cycle predicates [di3cycle]/[di4cycle] are genuine
        refinements of [dicycle] (and mutually exclusive);
      - the degreewidth Δ* is bounded by the identity order's back-degree (it really is a
        min over orders), and [has_LFO ⟹ Δ* ≤ 2] (the proved reduction, re-exposed as a
        clean edge);
      - concrete ordered twin-width refines (unordered) [tww_le] (the twinwidth_ordered ↔
        twinwidth bridge).

    The marquee non-transitive value Δ*(C₃) = 1 and has_LFO(C₃) (the directed triangle's
    single-back-arc order is a linear forest) are now PROVED in grounding_degreewidth_c3.v. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_fingroup all_algebra.
From Digraph Require Import prelude interop_graph_theory digraph oriented dipath.
From Digraph Require Import tournament order dichromatic omegabar.
From Digraph Require Import path_fas twinwidth twinwidth_ordered.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** [di3cycle] / [di4cycle] are genuine length-refined directed cycles *)

Lemma gr_di3cycle_dicycle (D : diGraphType) (c : seq D) : di3cycle c -> dicycle c.
Proof. by case/andP. Qed.

Lemma gr_di3cycle_size (D : diGraphType) (c : seq D) : di3cycle c -> size c = 3.
Proof. by case/andP=> _ /eqP. Qed.

Lemma gr_di4cycle_dicycle (D : diGraphType) (c : seq D) : di4cycle c -> dicycle c.
Proof. by case/andP. Qed.

(** A directed 3-cycle is not a directed 4-cycle: the length-3 and length-4 predicates are
    mutually exclusive, so they genuinely partition cycle lengths. *)
Lemma gr_di3_not_di4 (D : diGraphType) (c : seq D) : di3cycle c -> ~~ di4cycle c.
Proof. by case/andP=> _ /eqP s3; rewrite /di4cycle s3 andbF. Qed.

(** ** Degreewidth Δ* is a genuine minimum over orders *)

(** Δ*(T) ≤ the maximum back-degree under the identity order — the identity is an
    upper-bound witness, confirming Δ* = min over orders (via [Delta_star_min]). *)
Lemma gr_Delta_star_le_id (T : tournament) :
  (Delta_star T <= maxbackdeg (1%g : {perm T}))%N.
Proof. exact: Delta_star_min. Qed.

(** [has_LFO ⟹ Δ* ≤ 2]: a linear-forest order has max back-degree ≤ 2, so degreewidth ≤ 2.
    The proved Path-FAS reduction [has_LFO_Delta_star_le2], re-exposed as a clean edge. *)
Lemma gr_has_LFO_Delta_le2 (T : tournament) : has_LFO T -> (Delta_star T <= 2)%N.
Proof. exact: has_LFO_Delta_star_le2. Qed.

(** ** Concrete ordered twin-width refines (unordered) twin-width

    An ordered contraction sequence IS a contraction sequence, so a concrete ordered-tww
    bound entails the [tww_le] bound — the twinwidth_ordered ↔ twinwidth bridge
    ([concrete_otww_dominates_tww]). *)
Lemma gr_concrete_otww_refines (T : tournament) (p : {perm T}) (k : nat) :
  concrete_otww_le p k -> tww_le T k.
Proof. exact: concrete_otww_dominates_tww. Qed.
