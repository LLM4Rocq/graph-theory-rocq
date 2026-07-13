(** * GTMisc.conjectures.X74 -- v2 induced linear forest row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X74 vocabulary ************************************************)

Definition x74_min_degree_at_least (G : sgraph) (d : nat) : Prop :=
  forall v : G, d <= #|N(v)|.

Definition x74_induced_linear_forest (G : sgraph) (S : {set G}) : Prop :=
  is_forest [set: induced S] /\
  forall v : induced S, #|N(v)| <= 2.

Definition x74_degree_sum_den (G : sgraph) : nat :=
  \prod_(v : G) (#|N(v)|).+1.

Definition x74_scaled_degree_sum (G : sgraph) : nat :=
  \sum_(v : G) (2 * (x74_degree_sum_den G %/ (#|N(v)|).+1)).

(** ** X74 statements ******************************************************)

(** Studies slice: Akbari-Amanihamedani-Mousavi-Nikpey-Sheybani conjecture.
    The rational sum is represented with the common denominator
    product_v (d(v)+1). *)
Definition induced_linear_forest_caro_wei_bound_statement : Prop :=
  forall G : sgraph,
    x74_min_degree_at_least G 2 ->
    exists S : {set G},
      x74_induced_linear_forest S /\
      x74_scaled_degree_sum G <= x74_degree_sum_den G * #|S|.
