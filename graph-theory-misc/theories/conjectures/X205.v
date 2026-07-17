(** * GTMisc.conjectures.X205 -- v2 distributed list-colouring rounds row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X205 vocabulary ***********************************************)

Definition x205_delta_list_assignment (G : sgraph) :=
  G -> {set 'I_(Delta G).+1}.

Definition x205_valid_delta_lists (G : sgraph) (L : x205_delta_list_assignment G) : Prop :=
  forall v : G, (Delta G).+1 <= #|L v|.

Definition x205_list_colouring_output
    (G : sgraph) (L : x205_delta_list_assignment G) (col : G -> 'I_(Delta G).+1) : Prop :=
  (forall v : G, col v \in L v) /\
  (forall x y : G, x -- y -> col x != col y).

Record x205_randomized_local_algorithm (G : sgraph) (rounds : nat) := {
  x205_seed_space : finType;
  x205_output : x205_seed_space -> x205_delta_list_assignment G -> G -> 'I_(Delta G).+1;
  x205_success :
    forall L : x205_delta_list_assignment G,
      x205_valid_delta_lists L ->
      exists good : pred x205_seed_space,
        @fg_event_at_least_ratio x205_seed_space (fun _ => 1) good 2 3 /\
        forall s : x205_seed_space,
          good s -> x205_list_colouring_output L (x205_output s L)
}.

Definition x205_randomized_distributed_delta_list_colouring_fast
    (G : sgraph) (C : nat) : Prop :=
  exists rounds : nat,
    rounds <= C * (trunc_log 2 #|G|).+1 + C /\
    exists _ : x205_randomized_local_algorithm G rounds, True.

(** ** X205 statements *****************************************************)

(** Aboulker-Bonamy-Bousquet-Esperet question: whether randomized distributed
    list-colouring can avoid the multiplicative polynomial-in-[Delta] factor. *)
Definition randomized_distributed_delta_list_colouring_no_poly_delta_statement : Prop :=
  exists C : nat,
    forall G : sgraph,
      x205_randomized_distributed_delta_list_colouring_fast G C.
