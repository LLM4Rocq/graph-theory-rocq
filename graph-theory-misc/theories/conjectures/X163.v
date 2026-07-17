(** * GTMisc.conjectures.X163 -- v2 random graph normality row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X163 vocabulary ***********************************************)

Definition x163_stableb (G : sgraph) (S : {set G}) : bool :=
  [forall x in S, [forall y in S, (x == y) || ~~ (x -- y)]].

Definition x163_normal_graphb (G : sgraph) : bool :=
  [exists K : {set {set G}},
    [exists A : {set {set G}},
      [forall C in K, cliqueb C] &&
      [forall S in A, x163_stableb S] &&
      [forall v : G, [exists C in K, v \in C]] &&
      [forall v : G, [exists S in A, v \in S]] &&
      [forall C in K, [forall S in A, C :&: S != set0]]]].

Definition x163_random_graph_whp
    (p q : nat) (P : forall n : nat, pred {set {set 'I_n}}) : Prop :=
  @fg_whp (fun n : nat => {set {set 'I_n}}) (fun n => @fg_gnp_weight p q n) P.

(** ** X163 statements *****************************************************)

(** Open question: are random graphs G(n,p) normal with high probability?  The
    normality predicate is the clique-cover/stable-cover definition, and [G(n,p)]
    is counted exactly on labelled edge sets with rational edge probability [p/q]. *)
Definition random_graphs_normal_whp_statement : Prop :=
  forall p q : nat,
    0 < p ->
    p < q ->
    x163_random_graph_whp p q
      (fun n E => x163_normal_graphb (fg_labelled_sgraph E)).
