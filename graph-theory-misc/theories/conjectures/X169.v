(** * GTMisc.conjectures.X169 -- v2 token-sliding chordal algorithm row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X169 vocabulary ***********************************************)

Definition x169_tree_decomposition
    (G T : sgraph) (bag : T -> {set G}) : Prop :=
  is_tree [set: T] /\
  (forall v : G, exists t : T, v \in bag t) /\
  (forall x y : G, x -- y -> exists t : T, x \in bag t /\ y \in bag t) /\
  (forall v : G, connected [set t : T | v \in bag t]).

Definition x169_clique_tree (G T : sgraph) (bag : T -> {set G}) : Prop :=
  x169_tree_decomposition bag /\ forall t : T, cliqueb (bag t).

Definition x169_chordal (G : sgraph) : Prop :=
  exists (T : sgraph) (bag : T -> {set G}), x169_clique_tree bag.

Definition x169_clique_tree_degree_at_most (G : sgraph) (D : nat) : Prop :=
  exists (T : sgraph) (bag : T -> {set G}),
    x169_clique_tree bag /\ forall t : T, #|N(t)| <= D.

Definition x169_stable_set (G : sgraph) (S : {set G}) : Prop :=
  forall x y : G, x \in S -> y \in S -> x != y -> ~~ (x -- y).

Definition x169_ts_step (G : sgraph) (k : nat) : rel {set G} :=
  fun A B =>
    [exists a in A,
      [exists b : G,
        [&& b \notin A, a -- b, #|A| == k, #|B| == k &
            B == (A :\ a) :|: [set b]]]].

Definition x169_token_sliding_connected (G : sgraph) (k : nat) : Prop :=
  forall A B : {set G},
    x169_stable_set A -> #|A| = k ->
    x169_stable_set B -> #|B| = k ->
    exists p : seq {set G}, path (x169_ts_step k) A p /\ last A p = B.

Definition x169_polytime_decides_TS_connectivity (k D : nat) : Prop :=
  polytime_decides_graph_on
    (fun G : sgraph => x169_chordal G /\ x169_clique_tree_degree_at_most G D)
    (fun G : sgraph => x169_token_sliding_connected G k).

(** ** X169 statements *****************************************************)

(** Disproved question: for fixed k,D, can connectivity of the token-sliding
    reconfiguration graph TS_k(G) be decided in polynomial time on chordal graphs
    of clique-tree degree at most D? *)
Definition token_sliding_chordal_clique_tree_degree_polytime_statement : Prop :=
  forall k D : nat, x169_polytime_decides_TS_connectivity k D.
