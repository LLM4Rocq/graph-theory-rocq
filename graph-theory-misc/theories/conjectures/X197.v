(** * GTMisc.conjectures.X197 -- v2 planar cops capture time row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X197 vocabulary ***********************************************)

Definition x197_cop_position (G : sgraph) (cops : nat) := 'I_cops -> G.

Definition x197_captured (G : sgraph) (cops : nat)
    (C : x197_cop_position G cops) (r : G) : bool :=
  [exists i : 'I_cops, C i == r].

Definition x197_cop_move (G : sgraph) (cops : nat)
    (C C' : x197_cop_position G cops) : Prop :=
  forall i : 'I_cops, (C i == C' i) || (C i -- C' i).

Definition x197_robber_move (G : sgraph) (r r' : G) : Prop :=
  (r == r') || (r -- r').

Fixpoint x197_cops_win_in (G : sgraph) (cops t : nat)
    (C : x197_cop_position G cops) (r : G) {struct t} : Prop :=
  x197_captured C r \/
  if t is t'.+1 then
    exists C' : x197_cop_position G cops,
      x197_cop_move C C' /\
      forall r' : G, x197_robber_move r r' -> x197_cops_win_in t' C' r'
  else False.

Definition x197_capture_time (G : sgraph) (cops : nat) (t : nat) : Prop :=
  exists C0 : x197_cop_position G cops,
    (forall r0 : G, x197_cops_win_in t C0 r0) /\
    forall t' : nat, t' < t -> exists r0 : G, ~ x197_cops_win_in t' C0 r0.

(** ** X197 statements *****************************************************)

(** Bonato-Mohar question: is the bound [capt_3(G) <= 2n] tight for planar
    graphs, and in particular is there a planar graph with capture time greater
    than its order? *)
Definition planar_cops_capture_time_linear_tight_statement : Prop :=
  forall n0 : nat,
    exists (G : sgraph) (t : nat),
      [/\ n0 <= #|G|, wagner_planar G, #|G| < t & x197_capture_time G 3 t].
