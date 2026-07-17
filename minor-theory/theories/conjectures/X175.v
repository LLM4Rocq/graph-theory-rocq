(** * Minor.conjectures.X175 -- v2 clique count without K_t subdivision row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X175 vocabulary ***********************************************)

Definition x175_clique_count (G : sgraph) : nat :=
  #|[set S : {set G} | cliqueb S && (S != set0)]|.

Definition x175_path_internal {G : sgraph} (x y : G) (p : seq G) : {set G} :=
  [set z : G | (z \in x :: p) && (z != x) && (z != y)].

Definition x175_simple_path_between {G : sgraph} (x y : G) (p : seq G) : Prop :=
  [/\ uniq (x :: p), path (--) x p & last x p = y].

(** A subdivision of [K_t] in [G]: injective branch vertices, and internally
    vertex-disjoint simple paths between every branch pair. *)
Definition x175_Kt_subdivision (G : sgraph) (t : nat) : Prop :=
  exists branch : 'I_t -> G,
    injective branch /\
    exists route : 'I_t -> 'I_t -> seq G,
      [/\ (forall i j : 'I_t,
             i < j -> x175_simple_path_between (branch i) (branch j) (route i j)),
          (forall i j k : 'I_t,
             i < j ->
             branch k \notin x175_path_internal (branch i) (branch j) (route i j)) &
          forall i j i' j' : 'I_t,
             i < j -> i' < j' -> (i != i') || (j != j') ->
             [disjoint x175_path_internal (branch i) (branch j) (route i j) &
                       x175_path_internal (branch i') (branch j') (route i' j')]].

(** [3^(2t/3+o(t)) n] as the standard rational-epsilon eventual upper
    envelope.  For epsilon [a/b], raising to the positive power [3b] gives the
    finite integer inequality
    [cliques^(3b) <= 3^((2b+3a)t) * n^(3b)]. *)
Definition x175_subdivision_clique_asymptotic_bound
    (a b t n cliques : nat) : Prop :=
  cliques ^ (3 * b) <= (3 ^ ((2 * b + 3 * a) * t)) * (n ^ (3 * b)).

(** ** X175 statements *****************************************************)

(** Fox-Wei conjectured upper envelope: the optimal exponential constant for
    clique counts in graphs with no [K_t]-subdivision is
    [3^(2t/3+o(t)) n].  The known lower-bound construction is part of the
    source context; the open statement formalised here is the matching upper
    bound. *)
Definition kt_subdivision_clique_count_asymptotic_statement : Prop :=
  forall a b : nat,
    0 < a -> 0 < b ->
    eventually (fun t =>
      forall G : sgraph,
        ~ x175_Kt_subdivision G t ->
        x175_subdivision_clique_asymptotic_bound
          a b t #|G| (x175_clique_count G)).
