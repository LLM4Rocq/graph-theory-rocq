(** * GTBase.asymptotics -- package-neutral asymptotic vocabulary

    This module owns the elementary nat-valued "eventually" and Landau
    wrappers used by conjecture statements across the corpus.  The definitions
    are intentionally conservative: no limits, no reals, no axioms, and all
    constants and thresholds are explicit natural numbers.

    The rational-epsilon clauses are encoded by cross multiplication, so rows
    can state little-o or n^(1-o(1)) style hypotheses without importing an
    analytic library. *)

From mathcomp Require Import all_boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** [eventually P] means that [P n] holds for all sufficiently large [n]. *)
Definition eventually (P : nat -> Prop) : Prop :=
  exists N : nat, forall n : nat, N <= n -> P n.

Definition eventually_le (f g : nat -> nat) : Prop :=
  eventually (fun n => f n <= g n).

Definition eventually_ge (f g : nat -> nat) : Prop :=
  eventually (fun n => g n <= f n).

(** Nat-valued Landau envelopes.  [big_O_with_slack_nat] is useful when an
    additive constant is part of the faithful finite statement. *)
Definition big_O_nat (f g : nat -> nat) : Prop :=
  exists C : nat, 0 < C /\ eventually (fun n => f n <= C * g n).

Definition big_O_nat_from (f g : nat -> nat) (C N : nat) : Prop :=
  0 < C /\ forall n : nat, N <= n -> f n <= C * g n.

Definition big_O_with_slack_nat (f g : nat -> nat) : Prop :=
  exists C B : nat, 0 < C /\ eventually (fun n => f n <= C * g n + B).

Definition big_Omega_nat (f g : nat -> nat) : Prop := big_O_nat g f.

Definition big_Theta_nat (f g : nat -> nat) : Prop :=
  big_O_nat f g /\ big_O_nat g f.

(** [little_o_nat f g] renders [f(n) = o(g(n))] using rational epsilons
    [a / b > 0]: eventually [b * f n <= a * g n]. *)
Definition little_o_nat (f g : nat -> nat) : Prop :=
  forall a b : nat, 0 < a -> 0 < b ->
    eventually (fun n => b * f n <= a * g n).

(** Polynomial upper envelope with a bounded additive finite-size slack. *)
Definition polynomial_bound_nat (f : nat -> nat) : Prop :=
  exists C d B : nat, 0 < C /\
    eventually (fun n => f n <= C * n ^ d + B).

(** [subpolynomial_nat h] means [h(n) = n^o(1)], again using rational
    epsilons and cross multiplication. *)
Definition subpolynomial_nat (h : nat -> nat) : Prop :=
  forall a b : nat, 0 < a -> 0 < b ->
    eventually (fun n => (h n) ^ b <= n ^ a).

(** [near_linear_lower_nat h] means [h(n) >= n^(1-o(1))].  For each rational
    epsilon [a / b] with [0 < a < b], the eventual finite inequality is
    [n^(b-a) <= h(n)^b]. *)
Definition near_linear_lower_nat (h : nat -> nat) : Prop :=
  forall a b : nat, 0 < a -> a < b ->
    eventually (fun n => n ^ (b - a) <= (h n) ^ b).

(** Integer ceiling square root: the least [s] with [n <= s^2]. *)
Lemma sqrt_ceil_ex (n : nat) : exists s : nat, n <= s ^ 2.
Proof. exists n. by rewrite expnS expn1; case: n => // m; rewrite leq_pmulr. Qed.

Definition sqrt_ceil (n : nat) : nat := ex_minn (sqrt_ceil_ex n).

(** ** Grounding lemmas: the vocabulary is inhabited and behaves as intended. *)

Lemma eventually_intro (P : nat -> Prop) (N : nat) :
  (forall n : nat, N <= n -> P n) -> eventually P.
Proof. by exists N. Qed.

Lemma eventually_true : eventually (fun _ => True).
Proof. by exists 0. Qed.

Lemma eventually_mono (P Q : nat -> Prop) :
  eventually P -> (forall n : nat, P n -> Q n) -> eventually Q.
Proof. by move=> [N HP] HPQ; exists N => n Nn; apply: HPQ; apply: HP. Qed.

Lemma eventually_and (P Q : nat -> Prop) :
  eventually P -> eventually Q -> eventually (fun n => P n /\ Q n).
Proof.
move=> [NP HP] [NQ HQ]; exists (maxn NP NQ) => n Hn; split.
  exact: HP (leq_trans (leq_maxl NP NQ) Hn).
exact: HQ (leq_trans (leq_maxr NP NQ) Hn).
Qed.

Lemma big_O_nat_intro (f g : nat -> nat) (C N : nat) :
  0 < C ->
  (forall n : nat, N <= n -> f n <= C * g n) ->
  big_O_nat f g.
Proof. by move=> Cpos H; exists C; split=> //; exists N. Qed.

Lemma big_O_nat_refl (f : nat -> nat) : big_O_nat f f.
Proof. by exists 1; split=> //; exists 0 => n _; rewrite mul1n. Qed.

Lemma big_Theta_nat_refl (f : nat -> nat) : big_Theta_nat f f.
Proof. by split; apply: big_O_nat_refl. Qed.

Lemma big_O_nat_2n_n : big_O_nat (fun n => 2 * n) (fun n => n).
Proof. by exists 2; split=> //; exists 0 => n _. Qed.

Lemma big_O_nat_n_2n : big_O_nat (fun n => n) (fun n => 2 * n).
Proof.
exists 1; split=> //; exists 0 => n _.
by rewrite mul1n mulnC leq_pmulr.
Qed.

Lemma big_Theta_nat_2n_n : big_Theta_nat (fun n => 2 * n) (fun n => n).
Proof. by split; [exact: big_O_nat_2n_n | exact: big_O_nat_n_2n]. Qed.

Lemma little_o_zero_nat (g : nat -> nat) : little_o_nat (fun _ => 0) g.
Proof. by move=> a b _ _; exists 0 => n _; rewrite muln0. Qed.

Lemma polynomial_bound_nat_const (c : nat) : polynomial_bound_nat (fun _ => c).
Proof. by exists 1, 0, c; split=> //; exists 0 => n _; rewrite expn0 muln1 addnC leq_addr. Qed.

Lemma sqrt_ceil_spec (n : nat) : n <= (sqrt_ceil n) ^ 2.
Proof. by rewrite /sqrt_ceil; case: (ex_minnP (sqrt_ceil_ex n)). Qed.
