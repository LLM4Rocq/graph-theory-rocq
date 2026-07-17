(** * GTMisc.conjectures.X146 -- v2 Geelen coarse Gallai row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X146 vocabulary ***********************************************)

Fixpoint x146_ball (G : sgraph) (r : nat) (x : G) : {set G} :=
  if r is r'.+1 then x146_ball r' x :|: \bigcup_(z in x146_ball r' x) N(z)
  else [set x].

Definition x146_set_ball (G : sgraph) (r : nat) (S : {set G}) : {set G} :=
  \bigcup_(x in S) x146_ball r x.

Definition x146_path_vertices (G : sgraph) (p : seq G) : {set G} :=
  [set v | v \in p].

Definition x146_A_path (G : sgraph) (A : {set G}) (p : seq G) : Prop :=
  match p with
  | [::] => False
  | x :: q =>
      x \in A /\
      last x q \in A /\
      x != last x q /\
      uniq p /\
      path (--) x q /\
      forall v : G, v \in q -> v != last x q -> v \notin A
  end.

Definition x146_pairwise_distant_A_paths
    (G : sgraph) (d : nat) (paths : seq (seq G)) : Prop :=
  forall p q : seq G,
    p \in paths -> q \in paths -> p != q ->
    [disjoint x146_path_vertices p & x146_path_vertices q] /\
    [disjoint x146_set_ball (d.-1) (x146_path_vertices p) & x146_path_vertices q].

Definition x146_has_k_distant_A_paths
    (G : sgraph) (A : {set G}) (d k : nat) : Prop :=
  exists paths : seq (seq G),
    size paths = k /\
    uniq paths /\
    (forall p : seq G, p \in paths -> x146_A_path A p) /\
    x146_pairwise_distant_A_paths d paths.

Definition x146_every_A_path_hits_ball
    (G : sgraph) (A Z : {set G}) (r : nat) : Prop :=
  forall p : seq G,
    x146_A_path A p ->
    exists v : G,
      v \in x146_path_vertices p /\ v \in x146_set_ball r Z.

(** ** X146 statements *****************************************************)

(** Geelen coarse Gallai: either there are k pairwise distance-at-least-d
    A-paths, or a bounded set Z has a g(d)-neighbourhood meeting every A-path. *)
Definition geelen_coarse_gallai_A_paths_statement : Prop :=
  exists f g : nat -> nat,
    forall (k d : nat) (G : sgraph) (A : {set G}),
      1 <= k ->
      1 <= d ->
      x146_has_k_distant_A_paths A d k \/
      exists Z : {set G},
        #|Z| <= f k /\
        x146_every_A_path_hits_ball A Z (g d).

