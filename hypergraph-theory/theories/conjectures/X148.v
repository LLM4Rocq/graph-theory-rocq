(** * Hypergraph.conjectures.X148 -- v2 two-families/AK-bound row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X148 vocabulary ***********************************************)

Definition x148_two_families_hypotheses
    (I T : finType) (A B : I -> {set T}) : Prop :=
  (forall i : I, [disjoint A i & B i]) /\
  (forall i j : I, i != j -> ~~ [disjoint A i & B j]).

Definition x148_t_intersecting_first_family
    (I T : finType) (A : I -> {set T}) (t : nat) : Prop :=
  forall i j : I, i != j -> t <= #|A i :&: A j|.

Definition x148_AK_family_size (n t r : nat) : nat :=
  #|[set S : {set 'I_n} |
      t + r <= #|S :&: [set j : 'I_n | j < t + 2 * r]|]|.

Definition x148_AK_bound (n t : nat) : nat :=
  \max_(r < n.+1) x148_AK_family_size n t r.

(** ** X148 statements *****************************************************)

(** Gerbner-Keszegh-Methuku-Abhishek-Nagy-Patkos-Tompkins-Xiao: two-family
    systems satisfying Bollobas-type hypotheses and a first-family intersection
    condition obey the Ahlswede-Khachatrian t-intersecting bound. *)
Definition gerbner_two_families_ahlswede_khachatrian_bound_statement : Prop :=
  forall (t n : nat) (I T : finType) (A B : I -> {set T}),
    #|T| = n ->
    x148_two_families_hypotheses A B ->
    x148_t_intersecting_first_family A t ->
    #|I| <= x148_AK_bound n t.
