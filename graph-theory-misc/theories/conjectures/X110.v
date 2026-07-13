(** * GTMisc.conjectures.X110 -- v2 guarded Chen-Chvatal row *)

From mathcomp Require Import all_boot.
From GTMisc.conjectures Require Import X55.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X110 statements *****************************************************)

(** Studies slice: Chen-Chvatal metric-space de Bruijn-Erdos conjecture in
    its canonical n >= 2 form.  The metric-line vocabulary is reused from X55. *)
Definition chen_chvatal_guarded_metric_lines_statement : Prop :=
  forall (V : finType) (d : V -> V -> nat),
    (2 <= #|V|)%N ->
    x55_metric d ->
    x55_universal_line d \/ #|V| <= #|x55_lines d|.
