(** * Packing.conjectures.X155 -- v2 identifying-code VC dichotomy row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X155 vocabulary ***********************************************)

Definition x155_hereditary_class (C : sgraph -> Prop) : Prop :=
  forall (G : sgraph) (S : {set G}), C G -> C (induced S).

Definition x155_closed_neighbourhood (G : sgraph) (v : G) : {set G} :=
  [set v] :|: N(v).

Definition x155_identifying_code (G : sgraph) (Code : {set G}) : Prop :=
  (forall v : G, Code :&: x155_closed_neighbourhood v != set0) /\
  forall u v : G,
    u != v ->
    Code :&: x155_closed_neighbourhood u != Code :&: x155_closed_neighbourhood v.

Definition x155_identifying_code_number_at_least (G : sgraph) (m : nat) : Prop :=
  forall Code : {set G}, x155_identifying_code Code -> m <= #|Code|.

Definition x155_identifying_code_number_at_most (G : sgraph) (m : nat) : Prop :=
  exists Code : {set G}, x155_identifying_code Code /\ #|Code| <= m.

Definition x155_shatters (G : sgraph) (S : {set G}) : Prop :=
  forall A : {set G},
    A \subset S ->
    exists v : G, x155_closed_neighbourhood v :&: S = A.

Definition x155_vc_dimension_at_most (C : sgraph -> Prop) (d : nat) : Prop :=
  forall (G : sgraph) (S : {set G}), C G -> x155_shatters S -> #|S| <= d.

Definition x155_log_lower_bound (C : sgraph -> Prop) : Prop :=
  forall n : nat,
    exists G : sgraph,
      C G /\ n <= #|G| /\ x155_identifying_code_number_at_least G (trunc_log 2 n).+1.

Definition x155_polynomial_lower_bound (C : sgraph -> Prop) : Prop :=
  exists e : nat,
    0 < e /\
    forall n : nat,
      exists G : sgraph,
        C G /\ n <= #|G| /\ x155_identifying_code_number_at_least G (n ^ e).

Definition x155_constant_factor_approximation_with (K : nat) (C : sgraph -> Prop) : Prop :=
  exists opt : sgraph -> nat,
    (forall G : sgraph, C G -> x155_identifying_code_number_at_most G (opt G)) /\
    polytime_outputs_graph_on C
      (fun G out =>
        exists Code : {set G},
          x155_identifying_code Code /\
          #|Code| <= K * (opt G).+1 /\
          data_nat_value out = #|Code|).

Definition x155_log_APX_hard (C : sgraph -> Prop) : Prop :=
  forall K : nat, 0 < K -> ~ x155_constant_factor_approximation_with K C.

Definition x155_constant_factor_approximation (C : sgraph -> Prop) : Prop :=
  exists K : nat, 0 < K /\ x155_constant_factor_approximation_with K C.

(** ** X155 statements *****************************************************)

(** VC-dimension dichotomy for identifying codes on hereditary graph classes. *)
Definition identifying_code_vc_dimension_approximation_dichotomy_statement : Prop :=
  forall C : sgraph -> Prop,
    x155_hereditary_class C ->
    (x155_log_lower_bound C /\ x155_log_APX_hard C) \/
    (x155_polynomial_lower_bound C /\ x155_constant_factor_approximation C).
