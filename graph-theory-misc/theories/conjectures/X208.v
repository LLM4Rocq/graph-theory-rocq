(** * GTMisc.conjectures.X208 -- v2 MIS on P_t-free graphs row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X208 vocabulary ***********************************************)

Definition x208_induced_path_order (G : sgraph) (t : nat) : Prop :=
  exists (x : G) (p : seq G),
    [/\ size (x :: p) = t,
        path (--) x p,
        uniq (x :: p) &
        forall i j : nat,
          i.+1 < j -> j < size (x :: p) ->
          ~~ (nth x (x :: p) i -- nth x (x :: p) j)].

Definition x208_Pt_free (G : sgraph) (t : nat) : Prop :=
  ~ x208_induced_path_order G t.

Definition x208_stable_set (G : sgraph) (S : {set G}) : Prop :=
  forall x y : G, x \in S -> y \in S -> x != y -> ~~ (x -- y).

Definition x208_maximum_independent_set_output (G : sgraph) (out : data) : Prop :=
  exists S : {set G},
    x208_stable_set S /\
    #|S| = data_nat_value out /\
    forall T : {set G}, x208_stable_set T -> #|T| <= #|S|.

Definition x208_polytime_mis_on (P : sgraph -> Prop) : Prop :=
  polytime_outputs_graph_on P x208_maximum_independent_set_output.

(** ** X208 statements *****************************************************)

(** Groenland-Okrasa-Rzazewski-Scott-Seymour-Spirkl open problem: determine
    whether maximum independent set is polynomial-time decidable on [P_t]-free
    graphs for [t >= 7]. *)
Definition Pt_free_maximum_independent_set_polytime_statement : Prop :=
  forall t : nat, 7 <= t -> x208_polytime_mis_on (fun G => x208_Pt_free G t).
