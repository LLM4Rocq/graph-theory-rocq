(** * Hypergraph.conjectures.XE2 -- Erdos solved clean/bounded rows *)

From GTBase Require Export base.
From Hypergraph.conjectures Require Import X6.
From Hypergraph.conjectures Require Import XE1.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition xe2_hyperclique (T : finType) (E : {set {set T}}) (S : {set T}) : Prop :=
  forall e : {set T}, e \subset S -> #|e| = 3 -> e \in E.

Definition xe2_maximal_hyperclique
    (T : finType) (E : {set {set T}}) (S : {set T}) : Prop :=
  xe2_hyperclique E S /\
  forall U : {set T}, S \proper U -> ~ xe2_hyperclique E U.

Definition xe2_clique_size_set (T : finType) (E : {set {set T}}) (L : seq nat) : Prop :=
  uniq L /\
  forall q : nat,
    q \in L <->
    exists S : {set T}, xe2_maximal_hyperclique E S /\ #|S| = q.

Definition xe2_complete_uniform_on
    (T : finType) (E : {set {set T}}) (r : nat) (S : {set T}) : Prop :=
  E = [set e : {set T} | (e \subset S) && (#|e| == r)].

Definition xe2_fractional_exponential_degree
    (cnum cden r d : nat) : Prop :=
  0 < cden /\ cden ^ r * d >= (cden + cnum) ^ r.

(** Erdos Problems #775. *)
Definition erdos_775_statement : Prop :=
  exists C : nat,
    forall n : nat, exists (T : finType) (E : {set {set T}}) (L : seq nat),
      #|T| = n /\
      x6_uniform E 3 /\
      xe2_clique_size_set E L /\
      n <= size L + C.

(** Erdos Problems #832. *)
Definition erdos_832_statement : Prop :=
  forall r : nat, 3 <= r ->
    exists K : nat,
      forall (k : nat) (T : finType) (E : {set {set T}}),
        K <= k ->
        x6_uniform E r ->
        x6_chromatic_number E k ->
        'C((r - 1) * (k - 1) + 1, r) <= #|E| /\
        (#|E| = 'C((r - 1) * (k - 1) + 1, r) ->
          exists S : {set T},
            #|S| = (r - 1) * (k - 1) + 1 /\
            xe2_complete_uniform_on E r S).

(** Erdos Problems #833. *)
Definition erdos_833_statement : Prop :=
  exists cnum cden : nat,
    0 < cnum /\ 0 < cden /\
    forall (r : nat) (T : finType) (E : {set {set T}}),
      2 <= r ->
      x6_uniform E r ->
      x6_chromatic_number E 3 ->
      exists v : T,
        xe2_fractional_exponential_degree cnum cden r (x6_hg_degree E v).
