(** * Minor.conjectures.X198 -- v2 island colouring number row *)

From GraphTheory Require Import minor.
From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X198 vocabulary ***********************************************)

Definition x198_t_island (G : sgraph) (S : {set G}) (t : nat) : Prop :=
  S != set0 /\
  forall v : G, v \in S -> #|N(v) :\: S| < t.

Definition x198_col_star_le (C : sgraph -> Prop) (t : nat) : Prop :=
  exists c : nat,
    0 < c /\
    forall (G : sgraph) (A : {set G}),
      C G -> A != set0 ->
      exists S : {set induced A},
        #|S| <= c /\ @x198_t_island (induced A) S t.

Definition x198_join_path_rel (t m : nat) : rel ('I_t.-1 + 'I_m) :=
  fun x y =>
    match x, y with
    | inl _, inl _ => false
    | inl _, inr _ | inr _, inl _ => true
    | inr i, inr j => ((val i).+1 == val j) || ((val j).+1 == val i)
    end.

Definition x198_join_path (t m : nat) : sgraph :=
  @fg_mk_sgraph ('I_t.-1 + 'I_m)%type (@x198_join_path_rel t m).

Definition x198_forbids_Ktm_and_join_path
    (C : sgraph -> Prop) (t m : nat) : Prop :=
  1 <= m /\
  forall G : sgraph,
    C G -> ~ minor G (KB t m) /\ ~ minor G (x198_join_path t m).

(** ** X198 statements *****************************************************)

(** Dvorak-Norin Conjecture 4: for minor-closed classes, [col^* <= t] iff a
    finite obstruction condition excludes [K_{t,m}] and [I_{t-1}+P_m]. *)
(** The [1 <= t] guard is LOAD-BEARING: at t = 0 the source's I_{t-1} is
    undefined and the encoding's 'I_(t.-1) = 'I_0 makes the iff refutable
    axiom-free (single-vertex minor-closed class); the source's domain is
    t >= 1 (verify fix 2026-07-18, meta/BLOCKED_RETARGETING_AUDIT.md,
    repaired-rows section). *)
Definition minor_closed_col_star_obstruction_statement : Prop :=
  forall (C : sgraph -> Prop) (t : nat),
    1 <= t ->
    (forall G H : sgraph, C G -> minor G H -> C H) ->
    x198_col_star_le C t <->
    exists m : nat, x198_forbids_Ktm_and_join_path C t m.
