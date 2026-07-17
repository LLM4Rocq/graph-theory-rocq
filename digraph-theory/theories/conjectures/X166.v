(** * Digraph.conjectures.X166 -- v2 disjoint paths NP-completeness row *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph.
From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X166 vocabulary ***********************************************)

Definition x166_stable_set (D : diGraphType) (S : {set D}) : Prop :=
  forall x y : D,
    x \in S -> y \in S -> x != y -> ~~ (x --> y) /\ ~~ (y --> x).

Definition x166_stability_number_two (D : diGraphType) : Prop :=
  (exists S : {set D}, x166_stable_set S /\ #|S| = 2) /\
  forall S : {set D}, x166_stable_set S -> #|S| <= 2.

Definition x166_instance (k : nat) := {D : diGraphType & 'I_k -> (D * D)%type}.

Definition x166_enc_digraph (D : diGraphType) : data :=
  enc_list [seq enc_list [seq enc_bool (i --> j) | j <- enum D] | i <- enum D].

Definition x166_enc_instance (k : nat) (I : x166_instance k) : data :=
  x166_enc_digraph (projT1 I).

Definition x166_directed_path (D : diGraphType) (s t : D) (p : seq D) : Prop :=
  path (fun x y => x --> y) s p /\ last s p = t /\ uniq (s :: p).

Definition x166_internals (D : diGraphType) (s t : D) (p : seq D) : {set D} :=
  [set x : D | (x \in p) && (x != t)].

Definition x166_vertex_disjoint_directed_paths (k : nat) (I : x166_instance k) : Prop :=
  let D := projT1 I in
  let pairs := projT2 I in
  exists paths : forall i : 'I_k, seq D,
    (forall i : 'I_k, x166_directed_path (pairs i).1 (pairs i).2 (paths i)) /\
    forall i j : 'I_k, i != j ->
      x166_internals (pairs i).1 (pairs i).2 (paths i) :&:
      x166_internals (pairs j).1 (pairs j).2 (paths j) = set0.

Definition x166_in_np (k : nat) (P : x166_instance k -> Prop) : Prop :=
  exists cert_enc : x166_instance k -> data -> Prop,
    polytime_decides_on_class (@x166_enc_instance k)
      (fun _ => True) (fun I => exists c : data, cert_enc I c /\ P I).

Definition x166_np_hard (k : nat) (P : x166_instance k -> Prop) : Prop :=
  forall Q : x166_instance k -> Prop,
    @x166_in_np k Q ->
    exists red : prog,
      poly_cost_on (@x166_enc_instance k) red /\
      forall I : x166_instance k,
        prun red (@x166_enc_instance k I) = @x166_enc_instance k I /\ (Q I -> P I).

Definition x166_k_disjoint_paths_NP_complete_on_stability_two (k : nat) : Prop :=
  2 <= k /\
  @x166_in_np k (@x166_vertex_disjoint_directed_paths k) /\
  @x166_np_hard k (@x166_vertex_disjoint_directed_paths k) /\
  (forall I : x166_instance k,
    x166_stability_number_two (projT1 I) ->
    @x166_vertex_disjoint_directed_paths k I \/ ~ @x166_vertex_disjoint_directed_paths k I).

(** ** X166 statements *****************************************************)

(** Informal conjecture: the k vertex-disjoint paths problem might be
    NP-complete for digraphs with stability number two. *)
Definition vertex_disjoint_paths_stability_two_np_complete_statement : Prop :=
  exists k : nat, x166_k_disjoint_paths_NP_complete_on_stability_two k.
