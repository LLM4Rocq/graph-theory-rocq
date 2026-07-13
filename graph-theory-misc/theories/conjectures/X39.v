(** * GTMisc.conjectures.X39 -- v2 coarse Menger row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X39 vocabulary ************************************************)

Fixpoint x39_ball (G : sgraph) (r : nat) (x : G) : {set G} :=
  if r is r'.+1 then x39_ball r' x :|: \bigcup_(z in x39_ball r' x) N(z)
  else [set x].

Definition x39_set_ball (G : sgraph) (r : nat) (S : {set G}) : {set G} :=
  \bigcup_(x in S) x39_ball r x.

Definition x39_path_vertices (G : sgraph) (p : seq G) : {set G} :=
  [set v | v \in p].

Definition x39_xy_path (G : sgraph) (X Y : {set G}) (p : seq G) : Prop :=
  match p with
  | [::] => False
  | x :: q => x \in X /\ last x q \in Y /\ uniq p /\ path (--) x q
  end.

Definition x39_pairwise_distant_paths
    (G : sgraph) (d : nat) (paths : seq (seq G)) : Prop :=
  forall p q : seq G,
    p \in paths -> q \in paths -> p != q ->
    [disjoint x39_path_vertices p & x39_path_vertices q] /\
    [disjoint x39_set_ball (d.-1) (x39_path_vertices p) & x39_path_vertices q].

Definition x39_has_k_distant_xy_paths
    (G : sgraph) (d k : nat) (X Y : {set G}) : Prop :=
  exists paths : seq (seq G),
    size paths = k /\
    uniq paths /\
    (forall p : seq G, p \in paths -> x39_xy_path X Y p) /\
    x39_pairwise_distant_paths d paths.

Definition x39_separates_xy
    (G : sgraph) (X Y A : {set G}) : Prop :=
  forall p : seq G,
    x39_xy_path X Y p ->
    [disjoint x39_path_vertices p & A] ->
    False.

(** ** X39 statements ******************************************************)

(** Studies slice: Georgakopoulos-Papasoglu coarse Menger conjecture. *)
Definition coarse_menger_ball_separator_statement : Prop :=
  forall k : nat, exists c : nat,
    forall (d : nat) (G : sgraph) (X Y : {set G}),
      x39_has_k_distant_xy_paths d k X Y \/
      exists Z : {set G},
        #|Z| < k /\
        x39_separates_xy X Y (x39_set_ball (c * d) Z).
