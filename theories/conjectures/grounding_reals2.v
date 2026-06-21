(** * Digraph.conjectures.grounding_reals2 — deeper grounding of the reals/growth layer

    Solo grounding pass (the round-3 agent for this cluster stalled on transient API
    rate-limiting before writing a file).  Complements pass-1 [grounding_reals.v] (which
    grounded the Θ-algebra reflexive/symmetric/transitive) with the CONCRETE anchors the
    [reals_growth.v] definitions must satisfy:
      - [log2] base values: log₂1 = 0, log₂2 = 1 (it really is the base-2 logarithm);
      - the √-envelopes [env_a]/[env_t] are nonnegative (they bound nat invariants);
      - [is_Theta] holds with EXPLICIT constants on a concrete sequence (2n = Θ(n)), so the
        Θ predicate is satisfiable, not vacuous;
      - [eulerian] is non-vacuous (the one-vertex digraph is Eulerian) — the antecedent
        class of the EC-log / SAD milestone is inhabited. *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude interop_graph_theory digraph oriented tournament dipath.
From Digraph Require Import dichromatic heroes chi_bounded sad unvd reals_growth.
From Stdlib Require Import Reals Lra.

Open Scope R_scope.
Delimit Scope nat_scope with N.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** [log2] base values — it is the genuine base-2 logarithm *)

Lemma gr_log2_1 : log2 1 = 0.
Proof. by rewrite /log2 ln_1 /Rdiv Rmult_0_l. Qed.

Lemma gr_log2_2 : log2 2 = 1.
Proof.
have l2 : ln 2 <> 0.
  apply: Rgt_not_eq; have := ln_increasing 1 2; rewrite ln_1; apply; lra.
by rewrite /log2 /Rdiv; apply: Rinv_r.
Qed.

(** ** The √-envelopes are nonnegative (they bound nonnegative nat invariants) *)

Lemma gr_env_a_pos (n : nat) : 0 <= env_a n.
Proof. exact: sqrt_pos. Qed.

Lemma gr_env_t_pos (n : nat) : 0 <= env_t n.
Proof. exact: sqrt_pos. Qed.

(** ** [is_Theta] is satisfiable with explicit constants: 2·n = Θ(n)

    Witnesses [c1 = 1], [c2 = 2], threshold [N = 0]: for all n, 1·n ≤ 2·n ≤ 2·n (using
    n = INR n ≥ 0).  Confirms the Θ predicate is non-degenerate. *)
Lemma gr_Theta_2n_n : is_Theta (fun n => 2 * INR n) (fun n => INR n).
Proof.
exists 1, 2, 0%N; split; [lra | lra |].
by move=> n _; have := pos_INR n; lra.
Qed.

(** ** [eulerian] is non-vacuous: the one-vertex digraph is Eulerian

    [TT 1] has no arcs, so every vertex has in-degree = out-degree = 0.  This inhabits the
    antecedent class of [ec_log_statement] / [ec_log_gives_SAD]. *)
Lemma gr_eulerian_TT1 : eulerian (TT 1).
Proof.
move=> v; rewrite /indeg /outdeg.
have hf : forall a b : TT 1, (a --> b) = false.
  by move=> a b; rewrite (ord1 a) (ord1 b) arc_irrefl.
transitivity 0%N.
  by apply/eqP; rewrite cards_eq0; apply/eqP/setP=> w; rewrite !inE hf.
by symmetry; apply/eqP; rewrite cards_eq0; apply/eqP/setP=> w; rewrite !inE hf.
Qed.
