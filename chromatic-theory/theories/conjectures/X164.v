(** * Chromatic.conjectures.X164 -- v2 fixed-surface 3-colouring output row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X164 vocabulary ***********************************************)

Definition x164_embedded_in_fixed_surface_with_boundary
    (surface boundary : nat) (G : sgraph) : Prop :=
  surface_embeddable surface G.

Definition x164_instance : Type :=
  {G : sgraph & {B : {set G} & G -> 'I_3}}.

Definition x164_graph (I : x164_instance) : sgraph := projT1 I.
Definition x164_boundary (I : x164_instance) : {set x164_graph I} :=
  projT1 (projT2 I).
Definition x164_precolour (I : x164_instance) : x164_graph I -> 'I_3 :=
  projT2 (projT2 I).

Definition x164_enc_instance (I : x164_instance) : data :=
  Dpair (enc_graph (x164_graph I))
    (Dpair
      (enc_list [seq enc_bool (v \in x164_boundary I) | v <- enum (x164_graph I)])
      (enc_list [seq enc_nat (val (@x164_precolour I v)) | v <- enum (x164_graph I)])).

Fixpoint x164_data_nth_nat (d : data) (i : nat) : nat :=
  match d, i with
  | Dcons (Dnat n) _, 0 => n
  | Dcons _ rest, j.+1 => x164_data_nth_nat rest j
  | Dnat n, 0 => n
  | _, _ => 0
  end.

Definition x164_output_colour (I : x164_instance) (out : data)
    (v : x164_graph I) : nat :=
  x164_data_nth_nat out (enum_rank v) %% 3.

Definition x164_valid_output (I : x164_instance) (out : data) : Prop :=
  (forall x y : x164_graph I, x -- y ->
      @x164_output_colour I out x != @x164_output_colour I out y) /\
  (forall v : x164_graph I,
      v \in x164_boundary I ->
      @x164_output_colour I out v = val (@x164_precolour I v)).

Definition x164_instance_class (surface boundary : nat) (I : x164_instance) : Prop :=
  triangle_free (x164_graph I) /\
  x164_embedded_in_fixed_surface_with_boundary surface boundary (x164_graph I) /\
  #|x164_boundary I| <= boundary.

Definition x164_linear_time_outputs_three_colouring (surface boundary : nat) : Prop :=
  linear_time_outputs_on_class
    x164_enc_instance (x164_instance_class surface boundary) x164_valid_output.

(** ** X164 statements *****************************************************)

(** Open problem: output a 3-colouring of a triangle-free graph embedded in a
    fixed surface, with bounded precoloured boundary vertices, in linear time. *)
Definition linear_time_surface_triangle_free_three_colouring_output_statement : Prop :=
  forall surface boundary : nat,
    x164_linear_time_outputs_three_colouring surface boundary.
