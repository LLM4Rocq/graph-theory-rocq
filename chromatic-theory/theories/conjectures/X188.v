(** * Chromatic.conjectures.X188 -- v2 interactive sum-choice row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X188 vocabulary ***********************************************)

Definition x188_size_choosable (G : sgraph) (f : G -> nat) : Prop :=
  forall (C : finType) (L : G -> {set C}),
    (forall v : G, #|L v| = f v) -> @list_colourable G C L.

Definition x188_sum_choice_at_most (G : sgraph) (k : nat) : Prop :=
  exists f : G -> nat,
    (\sum_(v : G) f v) <= k /\ x188_size_choosable f.

Definition x188_sum_choice_number (G : sgraph) (k : nat) : Prop :=
  x188_sum_choice_at_most G k /\
  forall j : nat, x188_sum_choice_at_most G j -> k <= j.

Definition x188_add_colour (G : sgraph) (k : nat)
    (L : G -> {set 'I_k}) (v : G) (c : 'I_k) : G -> {set 'I_k} :=
  fun u : G => if u == v then L u :|: [set c] else L u.

Fixpoint x188_requester_wins
    (G : sgraph) (k fuel : nat) (L : G -> {set 'I_k}) : Prop :=
  @list_colourable G 'I_k L \/
  if fuel is fuel'.+1 then
    exists v : G,
      forall c : 'I_k,
        @x188_requester_wins G k fuel'
          (@x188_add_colour G k L v c)
  else False.

Definition x188_interactive_sum_choice_at_most (G : sgraph) (k : nat) : Prop :=
  @x188_requester_wins G k k (fun _ : G => set0).

Definition x188_interactive_sum_choice_number (G : sgraph) (k : nat) : Prop :=
  x188_interactive_sum_choice_at_most G k /\
  forall j : nat, x188_interactive_sum_choice_at_most G j -> k <= j.

Definition x188_component_not_complete (G : sgraph) : Prop :=
  exists (root : G) (S : {set G}),
    S = [set y : G | connect (--) root y] /\ ~ clique S.

(** ** X188 statements *****************************************************)

(** Bonamy-Meeks Conjecture 1.1: if some connected component of [G] is not a
    complete graph, then [chi_ISC(G) < chi_SC(G)]. *)
Definition interactive_sum_choice_strict_statement : Prop :=
  forall (G : sgraph) (isc sc : nat),
    x188_component_not_complete G ->
    x188_interactive_sum_choice_number G isc ->
    x188_sum_choice_number G sc ->
    isc < sc.
