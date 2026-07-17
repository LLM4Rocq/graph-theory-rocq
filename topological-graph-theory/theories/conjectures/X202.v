(** * Topological.conjectures.X202 -- v2 genus cop-number asymptotic row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X202 vocabulary ***********************************************)

Definition x202_cop_position (G : sgraph) (cops : nat) := 'I_cops -> G.

Definition x202_captured (G : sgraph) (cops : nat)
    (C : x202_cop_position G cops) (r : G) : bool :=
  [exists i : 'I_cops, C i == r].

Definition x202_cop_move (G : sgraph) (cops : nat)
    (C C' : x202_cop_position G cops) : Prop :=
  forall i : 'I_cops, (C i == C' i) || (C i -- C' i).

Definition x202_robber_move (G : sgraph) (r r' : G) : Prop :=
  (r == r') || (r -- r').

Fixpoint x202_cops_win_in (G : sgraph) (cops t : nat)
    (C : x202_cop_position G cops) (r : G) {struct t} : Prop :=
  x202_captured C r \/
  if t is t'.+1 then
    exists C' : x202_cop_position G cops,
      x202_cop_move C C' /\
      forall r' : G, x202_robber_move r r' -> x202_cops_win_in t' C' r'
  else False.

Definition x202_cop_number_at_most (G : sgraph) (cops : nat) : Prop :=
  exists (t : nat) (C0 : x202_cop_position G cops),
    forall r0 : G, x202_cops_win_in t C0 r0.

Definition x202_genus_cop_number_at_most (g cops : nat) : Prop :=
  forall G : sgraph, surface_embeddable g G -> x202_cop_number_at_most G cops.

Definition x202_cop_number_genus_window (g eps_num eps_den : nat) : Prop :=
  exists cops : nat,
    x202_genus_cop_number_at_most g cops /\
    eps_den * cops * cops <= (eps_den + eps_num) * g.+1.

(** ** X202 statements *****************************************************)

(** Mohar Conjecture 8: the orientable and nonorientable cop-number functions
    grow as [g^(1/2+o(1))], rendered by rational epsilon windows around the
    square-root scale. *)
Definition genus_cop_number_sqrt_asymptotic_statement : Prop :=
  forall eps_num eps_den : nat,
    0 < eps_num ->
    eps_num <= eps_den ->
    exists g0 : nat,
      forall g : nat,
        g0 <= g ->
        x202_cop_number_genus_window g eps_num eps_den.
