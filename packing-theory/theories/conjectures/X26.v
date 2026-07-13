(** * Packing.conjectures.X26 -- v2 distant induced-Menger row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X26 vocabulary ************************************************)

Fixpoint x26_ball (G : sgraph) (r : nat) (x : G) : {set G} :=
  if r is r'.+1 then x26_ball r' x :|: \bigcup_(z in x26_ball r' x) N(z)
  else [set x].

Definition x26_set_ball (G : sgraph) (r : nat) (S : {set G}) : {set G} :=
  \bigcup_(x in S) x26_ball r x.

Definition x26_path_vertices (G : sgraph) (p : seq G) : {set G} :=
  [set v | v \in p].

Definition x26_xy_path (G : sgraph) (X Y : {set G}) (p : seq G) : Prop :=
  match p with
  | [::] => False
  | x :: q => x \in X /\ last x q \in Y /\ uniq p /\ path (--) x q
  end.

Definition x26_pairwise_distant_paths
    (G : sgraph) (d : nat) (paths : seq (seq G)) : Prop :=
  forall p q : seq G,
    p \in paths -> q \in paths -> p != q ->
    [disjoint x26_set_ball (d.-1) (x26_path_vertices p) & x26_path_vertices q].

Definition x26_has_k_distant_xy_paths
    (G : sgraph) (d k : nat) (X Y : {set G}) : Prop :=
  exists paths : seq (seq G),
    size paths = k /\
    uniq paths /\
    (forall p : seq G, p \in paths -> x26_xy_path X Y p) /\
    x26_pairwise_distant_paths d paths.

Definition x26_separates_xy (G : sgraph) (X Y Z : {set G}) : Prop :=
  forall p : seq G,
    x26_xy_path X Y p ->
    [disjoint x26_path_vertices p & Z] ->
    False.

(** ** X26 statements ******************************************************)

(** arXiv:2309.07905, distant induced-Menger type conjecture. *)
Definition bounded_degree_distant_induced_menger_statement : Prop :=
  forall d Dmax : nat, exists C : nat,
    0 < C /\
    forall (k : nat) (G : sgraph) (X Y : {set G}),
      Delta G <= Dmax ->
      x26_has_k_distant_xy_paths d k X Y \/
      exists Z : {set G},
        #|Z| < C * k /\
        x26_separates_xy X Y Z.
