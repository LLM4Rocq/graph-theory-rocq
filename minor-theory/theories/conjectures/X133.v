(** * Minor.conjectures.X133 -- v2 K_s-free clique-minor growth row *)

From GraphTheory Require Import minor.
From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X133 vocabulary ***********************************************)

Definition x133_Ks_free (G : sgraph) (s : nat) : Prop :=
  ω([set: G]) < s.

(** ** X133 statements *****************************************************)

(** Dvorak-Yepremyan: for each fixed [s], every [K_s]-free [n]-vertex graph
    with independence number at most [r] and sufficiently large [n/r] has a
    clique minor polynomially larger than [n/r].  "Polynomially larger" is
    encoded as the existence of a positive rational epsilon = e1/e2 such that
    [t >= (n/r)^(1+epsilon)] for the clique-minor order [t], cross-multiplied:
    [n^(e2+e1) <= t^e2 * r^(e2+e1)]. *)
Definition dvorak_yepremyan_ks_free_clique_minor_polynomial_statement : Prop :=
  forall s : nat,
    1 < s ->
    exists e1 e2 N : nat,
      [/\ 0 < e1, 0 < e2 &
        forall (r n : nat) (G : sgraph),
          0 < r ->
          #|G| = n ->
          x133_Ks_free G s ->
          α(G) <= r ->
          N * r <= n ->
          exists t : nat,
            minor G 'K_t /\
            n ^ (e2 + e1) <= t ^ e2 * r ^ (e2 + e1)].

