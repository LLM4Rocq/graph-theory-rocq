(** * Chromatic.conjectures.X170 -- v2 oriented-P4 chi-boundedness row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X170 vocabulary ***********************************************)

Definition x170_oriented_P4_code := 'I_8.

Definition x170_nonexceptional (P : {set x170_oriented_P4_code}) : Prop :=
  P != set0 /\ P != [set inord 7] /\ P != [set ord0].

Record x170_oriented_graph := X170OrientedGraph {
  x170_underlying :> sgraph;
  x170_arc : x170_underlying -> x170_underlying -> bool;
  x170_arc_edge : forall u v : x170_underlying, x170_arc u v -> u -- v;
  x170_arc_orients :
    forall u v : x170_underlying, u -- v -> x170_arc u v = ~~ x170_arc v u
}.

Definition x170_p4_edge (i j : 'I_4) : bool :=
  ((val i).+1 == val j) || ((val j).+1 == val i).

Definition x170_code_forward (P : x170_oriented_P4_code) (i : 'I_3) : bool :=
  odd (val P %/ (2 ^ val i)).

Definition x170_induced_oriented_P4
    (O : x170_oriented_graph) (P : x170_oriented_P4_code) : Prop :=
  exists v : 'I_4 -> O,
    injective v /\
    (forall i j : 'I_4, (v i -- v j) = x170_p4_edge i j) /\
    (forall i : 'I_3,
      x170_arc (v (inord (val i))) (v (inord (val i).+1)) =
        x170_code_forward P i).

Definition x170_forb_oriented_P4_family
    (P : {set x170_oriented_P4_code}) (O : x170_oriented_graph) : Prop :=
  forall Q : x170_oriented_P4_code,
    Q \in P -> ~ x170_induced_oriented_P4 O Q.

Definition x170_chi_bounded (C : x170_oriented_graph -> Prop) : Prop :=
  exists f : nat -> nat,
    forall O : x170_oriented_graph,
      C O -> χ([set: x170_underlying O]) <= f (ω([set: x170_underlying O])).

(** ** X170 statements *****************************************************)

(** Conjecture 5: for non-empty nonexceptional subsets P of the eight orientations
    of P4, Forb(P) is chi-bounded. *)
Definition oriented_P4_forb_chi_bounded_statement : Prop :=
  forall P : {set x170_oriented_P4_code},
    x170_nonexceptional P ->
    x170_chi_bounded (x170_forb_oriented_P4_family P).
