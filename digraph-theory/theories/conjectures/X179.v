(** * Digraph.conjectures.X179 -- v2 kappa-maderian digraph row *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X179 vocabulary ***********************************************)

Definition x179_strongly_connected_after_deleting (G : diGraphType) (S : {set G}) : Prop :=
  forall x y : G,
    x \notin S -> y \notin S ->
    connect (fun u v => (u --> v) && (u \notin S) && (v \notin S)) x y.

Definition x179_k_vertex_strongly_connected (G : diGraphType) (k : nat) : Prop :=
  forall S : {set G}, #|S| < k -> x179_strongly_connected_after_deleting S.

Definition x179_out_cut (G : diGraphType) (S : {set G}) : {set G * G} :=
  [set e : G * G | (e.1 \in S) && (e.2 \notin S) && (e.1 --> e.2)].

Definition x179_k_arc_strongly_connected (G : diGraphType) (k : nat) : Prop :=
  forall S : {set G}, S != set0 -> S != [set: G] -> k <= #|x179_out_cut S|.

Definition x179_directed_path (G : diGraphType) (s t : G) (p : seq G) : Prop :=
  path (fun x y => x --> y) s p /\ last s p = t /\ uniq (s :: p).

Definition x179_directed_subdivision (G D : diGraphType) : Prop :=
  exists branch : D -> G,
    injective branch /\
    forall x y : D,
      x --> y ->
      exists p : seq G,
        x179_directed_path (branch x) (branch y) p /\
        forall z : G, z \in p -> z != branch y -> forall u : D, z != branch u.

Definition x179_kappa_maderian (D : diGraphType) : Prop :=
  exists k : nat,
    forall G : diGraphType,
      x179_k_vertex_strongly_connected G k -> x179_directed_subdivision G D.

Definition x179_arc_kappa_maderian (D : diGraphType) : Prop :=
  exists k : nat,
    forall G : diGraphType,
      x179_k_arc_strongly_connected G k -> x179_directed_subdivision G D.

(** ** X179 statements *****************************************************)

(** Problem 16 from Aboulker-Cohen-Havet-Lochet-Moura-Thomasse: are all
    digraphs kappa-maderian and kappa'-maderian? *)
Definition digraph_kappa_maderian_statement : Prop :=
  forall D : diGraphType,
    x179_kappa_maderian D /\ x179_arc_kappa_maderian D.
