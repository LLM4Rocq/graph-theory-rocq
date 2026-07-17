(** * Topological.conjectures.X176 -- v2 cone crossing asymptotic row *)

From GTBase Require Export base.
From Topological.foundations Require Import crossing.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X176 vocabulary ***********************************************)

Definition x176_cone_rel (G : sgraph) : rel (option G) :=
  fun x y =>
    match x, y with
    | Some u, Some v => u -- v
    | Some _, None | None, Some _ => true
    | None, None => false
    end.

Lemma x176_cone_rel_sym (G : sgraph) : symmetric (@x176_cone_rel G).
Proof. by move=> [x|] [y|] //=; rewrite sg_sym. Qed.

Lemma x176_cone_rel_irrefl (G : sgraph) : irreflexive (@x176_cone_rel G).
Proof. by move=> [x|] //=; rewrite sg_irrefl. Qed.

Definition x176_cone (G : sgraph) : sgraph :=
  SGraph (@x176_cone_rel_sym G) (@x176_cone_rel_irrefl G).

Definition x176_simple_cone_crossing_value (k n : nat) : Prop :=
  exists G : sgraph,
    is_crossing_number G k /\
    is_crossing_number (x176_cone G) n /\
    forall (H : sgraph) (m : nat),
      is_crossing_number H k ->
      is_crossing_number (x176_cone H) m ->
      n <= m.

Definition x176_target (k : nat) : nat :=
  k + sqrt_ceil (sqrt_ceil (2 * k ^ 3)).

Definition x176_abs_diff (f g : nat -> nat) (k : nat) : nat :=
  if f k <= g k then g k - f k else f k - g k.

Definition x176_cone_crossing_asymptotic (f : nat -> nat) : Prop :=
  little_o_nat (x176_abs_diff f x176_target) x176_target.

(** ** X176 statements *****************************************************)

(** Alfaro-Arroyo-Derunar-Mohar conjecture on the precise asymptotics of the
    simple cone crossing function [f_s(k)], using the existing split-crossing
    number relation and a root-free integer approximation to
    [sqrt(2) k^(3/4)]. *)
Definition simple_cone_crossing_function_asymptotic_statement : Prop :=
  exists f : nat -> nat,
    (forall k : nat, x176_simple_cone_crossing_value k (f k)) /\
    x176_cone_crossing_asymptotic f.
