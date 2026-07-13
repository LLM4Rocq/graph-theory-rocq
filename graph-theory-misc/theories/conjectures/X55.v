(** * GTMisc.conjectures.X55 -- v2 Chen-Chvatal metric-line row *)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X55 vocabulary ************************************************)

Definition x55_metric (V : finType) (d : V -> V -> nat) : Prop :=
  (forall x y : V, d x y = 0 <-> x = y) /\
  (forall x y : V, d x y = d y x) /\
  forall x y z : V, d x z <= d x y + d y z.

Definition x55_between (V : finType) (d : V -> V -> nat) (a b x : V) : bool :=
  (d a b == d a x + d x b) ||
  (d a x == d a b + d b x) ||
  (d b x == d b a + d a x).

Definition x55_line (V : finType) (d : V -> V -> nat) (a b : V) : {set V} :=
  [set x : V | x55_between d a b x].

Definition x55_universal_line (V : finType) (d : V -> V -> nat) : Prop :=
  exists a b : V, a != b /\ x55_line d a b = [set: V].

Definition x55_lines (V : finType) (d : V -> V -> nat) : {set {set V}} :=
  [set L : {set V} |
      [exists a : V, [exists b : V, (a != b) && (L == x55_line d a b)]]].

(** ** X55 statements ******************************************************)

(** Studies slice: Chen-Chvatal/de Bruijn-Erdos property for finite metric
    spaces. *)
Definition chen_chvatal_metric_lines_statement : Prop :=
  forall (V : finType) (d : V -> V -> nat),
    (2 <= #|V|)%N ->
    x55_metric d ->
    x55_universal_line d \/ #|V| <= #|x55_lines d|.
