(** * Minor.conjectures.X11 -- v2 minor/list and induced-Menger rows *)

From GraphTheory Require Import minor.
From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X11 vocabulary ************************************************)

Definition x11_path_vertices (G : sgraph) (p : seq G) : {set G} :=
  [set v | v \in p].

Definition x11_xy_path (G : sgraph) (X Y : {set G}) (p : seq G) : Prop :=
  match p with
  | [::] => False
  | x :: q =>
      x \in X /\ last x q \in Y /\ uniq p /\ path (--) x q
  end.

Definition x11_closed_neighbourhood (G : sgraph) (Z : {set G}) : {set G} :=
  Z :|: \bigcup_(z in Z) N(z).

Definition x11_anticomplete_sets (G : sgraph) (A B : {set G}) : Prop :=
  [disjoint A & B] /\
  forall x y : G, x \in A -> y \in B -> ~~ (x -- y).

Definition x11_pairwise_anticomplete_paths
    (G : sgraph) (paths : seq (seq G)) : Prop :=
  forall p q : seq G,
    p \in paths -> q \in paths -> p != q ->
    @x11_anticomplete_sets G (x11_path_vertices p) (x11_path_vertices q).

Definition x11_has_k_anticomplete_xy_paths
    (G : sgraph) (k : nat) (X Y : {set G}) : Prop :=
  exists paths : seq (seq G),
    size paths = k /\
    uniq paths /\
    (forall p : seq G, p \in paths -> @x11_xy_path G X Y p) /\
    @x11_pairwise_anticomplete_paths G paths.

Definition x11_no_xy_path_after_closed_neighbourhood
    (G : sgraph) (X Y Z : {set G}) : Prop :=
  forall p : seq G,
    @x11_xy_path G X Y p ->
    [disjoint x11_path_vertices p & x11_closed_neighbourhood Z] ->
    False.

(** ** X11 statements ******************************************************)

(** arXiv:2201.09115, fixed-s regime for Woodall's conjecture. *)
Definition woodall_fixed_s_eventual_choosability_statement : Prop :=
  forall s : nat, 1 <= s ->
    exists T : nat,
      s <= T /\
      forall (t ch : nat) (G : sgraph),
        T <= t ->
        ~ minor G (KB s t) ->
        is_choice_number G ch ->
        ch <= s + t - 1.

(** arXiv:2512.17232, Conjecture 6. *)
Definition induced_menger_anticomplete_paths_statement : Prop :=
  forall (k : nat) (G : sgraph) (X Y : {set G}),
    @x11_has_k_anticomplete_xy_paths G k X Y \/
    exists Z : {set G},
      #|Z| <= k.-1 /\
      @x11_no_xy_path_after_closed_neighbourhood G X Y Z.
