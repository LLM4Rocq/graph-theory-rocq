(** * Chromatic.conjectures.X157 -- v2 local-connectivity colouring algorithm row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X157 vocabulary ***********************************************)

Definition x157_path_internal (G : sgraph) (x y : G) (p : seq G) : {set G} :=
  [set z : G | z \in p] :\: [set x; y].

Definition x157_simple_xy_path (G : sgraph) (x y : G) (p : seq G) : Prop :=
  path (--) x p /\ last x p = y /\ uniq (x :: p).

Definition x157_internally_disjoint_xy_paths
    (G : sgraph) (x y : G) (m : nat) : Prop :=
  exists route : 'I_m -> seq G,
    (forall i : 'I_m, x157_simple_xy_path x y (route i)) /\
    forall i j : 'I_m,
      i != j ->
      [disjoint x157_path_internal x y (route i)
       & x157_path_internal x y (route j)].

Definition x157_max_local_connectivity_at_most (G : sgraph) (k : nat) : Prop :=
  forall (x y : G) (m : nat),
    x != y -> x157_internally_disjoint_xy_paths x y m -> m <= k.

Fixpoint x157_data_nth_nat (d : data) (i : nat) : nat :=
  match d, i with
  | Dcons (Dnat n) _, 0 => n
  | Dcons _ rest, j.+1 => x157_data_nth_nat rest j
  | Dnat n, 0 => n
  | _, _ => 0
  end.

Definition x157_output_colour (G : sgraph) (k : nat) (out : data) (v : G) : nat :=
  x157_data_nth_nat out (enum_rank v) %% k.

Definition x157_output_k_colouring_or_none
    (k : nat) (G : sgraph) (out : data) : Prop :=
  (out = Dnat 0 /\ ~ χ([set: G]) <= k) \/
  (0 < k /\ forall x y : G, x -- y ->
      x157_output_colour k out x != x157_output_colour k out y).

Definition x157_polytime_colouring_or_none (k : nat) : Prop :=
  polytime_outputs_graph_on
    (fun G : sgraph => k_connected G k /\ x157_max_local_connectivity_at_most G k)
    (x157_output_k_colouring_or_none k).

(** ** X157 statements *****************************************************)

(** Question 1.7: for fixed k>=4, decide/find k-colourability on k-connected
    graphs of maximal local connectivity k in polynomial time. *)
Definition local_connectivity_k_colouring_polytime_statement : Prop :=
  forall k : nat, 4 <= k -> x157_polytime_colouring_or_none k.
