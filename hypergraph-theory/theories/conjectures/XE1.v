(** * Hypergraph.conjectures.XE1 -- Erdos open clean/bounded rows *)

From Hypergraph.conjectures Require Import X6.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition xe1_complete_uniform_edges (T : finType) (r : nat) : {set {set T}} :=
  [set e : {set T} | #|e| == r].

Definition xe1_mono_3_clique (m n : nat) (col : {set 'I_m} -> bool) : Prop :=
  exists S : {set 'I_m},
    #|S| = n /\
    exists b : bool,
      forall e : {set 'I_m}, e \subset S -> #|e| = 3 -> col e = b.

Definition xe1_hypergraph_ramsey3 (n m : nat) : Prop :=
  forall col : {set 'I_m} -> bool, xe1_mono_3_clique n col.

Definition xe1_hypergraph_ramsey3_number (n m : nat) : Prop :=
  xe1_hypergraph_ramsey3 n m /\
  forall m' : nat, xe1_hypergraph_ramsey3 n m' -> m <= m'.

Definition xe1_contains_complete_uniform
    (T : finType) (E : {set {set T}}) (r q : nat) : Prop :=
  exists S : {set T},
    #|S| = q /\ forall e : {set T}, e \subset S -> #|e| = r -> e \in E.

Definition xe1_extremal_no_complete_uniform (n r q m : nat) : Prop :=
  (exists (T : finType) (E : {set {set T}}),
      [/\ #|T| = n, x6_uniform E r, ~ xe1_contains_complete_uniform E r q
        & #|E| = m]) /\
  forall m' : nat,
    (exists (T : finType) (E : {set {set T}}),
      [/\ #|T| = n, x6_uniform E r, ~ xe1_contains_complete_uniform E r q
        & #|E| = m']) ->
    m' <= m.

Definition xe1_complete_piece (T : finType) (E : {set {set T}}) (r : nat)
    (S : {set T}) : Prop :=
  (#|S| = r \/ #|S| = r.+1) /\
  forall e : {set T}, e \subset S -> #|e| = r -> e \in E.

Definition xe1_piece_covers_edge (T : finType) (r : nat)
    (P : {set T}) (e : {set T}) : Prop :=
  e \subset P /\ #|e| = r.

Definition xe1_pieces_pairwise_share_no_r_set
    (T : finType) (r m : nat) (P : 'I_m -> {set T}) : Prop :=
  forall i j : 'I_m, i != j ->
    forall e : {set T}, #|e| = r -> e \subset P i -> e \subset P j -> False.

Definition xe1_hypergraph_decomposition_bound
    (T : finType) (E : {set {set T}}) (r b : nat) : Prop :=
  exists m : nat, exists P : 'I_m -> {set T},
    m <= b /\
    (forall i : 'I_m, xe1_complete_piece E r (P i)) /\
    xe1_pieces_pairwise_share_no_r_set r P /\
    forall e : {set T}, e \in E -> exists i : 'I_m, xe1_piece_covers_edge r (P i) e.

Definition xe1_intersecting_hypergraph (T : finType) (E : {set {set T}}) : Prop :=
  forall e f : {set T}, e \in E -> f \in E -> e != f -> ~~ [disjoint e & f].

(** Erdős Problems #564. *)
Definition erdos_564_statement : Prop :=
  exists cnum cden N : nat,
    0 < cnum /\ 0 < cden /\
    forall n R : nat,
      N <= n ->
      xe1_hypergraph_ramsey3_number n R ->
      2 ^ (2 ^ ((cnum * n) %/ cden)) <= R.

(** Erdős Problems #719. *)
Definition erdos_719_statement : Prop :=
  forall (r n ex : nat) (T : finType) (E : {set {set T}}),
    2 <= r -> #|T| = n -> x6_uniform E r ->
    xe1_extremal_no_complete_uniform n r r.+1 ex ->
    xe1_hypergraph_decomposition_bound E r ex.

(** Erdős Problems #836. *)
Definition erdos_836_statement : Prop :=
  (exists C : nat,
      forall (r : nat) (T : finType) (E : {set {set T}}),
        2 <= r -> x6_uniform E r -> x6_chromatic_number E 3 ->
        xe1_intersecting_hypergraph E ->
        (forall v : T, exists e : {set T}, e \in E /\ v \in e) ->
        #|T| <= C * r ^ 2) /\
  (exists cnum cden : nat,
      0 < cnum /\ 0 < cden /\
      forall (r : nat) (T : finType) (E : {set {set T}}),
        2 <= r -> x6_uniform E r -> x6_chromatic_number E 3 ->
        xe1_intersecting_hypergraph E ->
        exists e f : {set T},
          e \in E /\ f \in E /\ e != f /\ cnum * r <= cden * #|e :&: f|).
