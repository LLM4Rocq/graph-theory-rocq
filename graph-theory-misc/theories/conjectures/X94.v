(** * GTMisc.conjectures.X94 -- v2 bipartite strong Erdos-Hajnal row *)

From HB Require Import structures.
From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X94 vocabulary ************************************************)

Record x94_bigraph := X94Bigraph {
  x94_left : finType;
  x94_right : finType;
  x94_biedge : x94_left -> x94_right -> bool
}.

Definition x94_vertices (B : x94_bigraph) : Type :=
  (x94_left B + x94_right B)%type.

HB.instance Definition _ (B : x94_bigraph) := Finite.on (x94_vertices B).

Definition x94_underlying_rel (B : x94_bigraph) : rel (x94_vertices B) :=
  fun u v =>
    match u, v with
    | inl x, inr y => @x94_biedge B x y
    | inr y, inl x => @x94_biedge B x y
    | _, _ => false
    end.

Lemma x94_underlying_sym (B : x94_bigraph) :
  symmetric (@x94_underlying_rel B).
Proof. by move=> [x|y] [x'|y']. Qed.

Lemma x94_underlying_irrefl (B : x94_bigraph) :
  irreflexive (@x94_underlying_rel B).
Proof. by move=> [x|y]. Qed.

Definition x94_underlying_graph (B : x94_bigraph) : sgraph :=
  SGraph (@x94_underlying_sym B) (@x94_underlying_irrefl B).

Definition x94_forest_bigraph (B : x94_bigraph) : Prop :=
  is_forest [set: @x94_underlying_graph B].

Definition x94_bicomplement (B : x94_bigraph) : x94_bigraph :=
  {| x94_left := x94_left B;
     x94_right := x94_right B;
     x94_biedge := fun x y => ~~ @x94_biedge B x y |}.

Definition x94_induced_copy (H G : x94_bigraph) : Prop :=
  exists (fL : x94_left H -> x94_left G)
         (fR : x94_right H -> x94_right G),
    injective fL /\
    injective fR /\
    forall x y : x94_left H * x94_right H,
      @x94_biedge H x.1 x.2 = @x94_biedge G (fL x.1) (fR x.2).

Definition x94_H_free (G H : x94_bigraph) : Prop :=
  ~ @x94_induced_copy H G.

Definition x94_complete_pair
    (G : x94_bigraph) (ZL : {set x94_left G}) (ZR : {set x94_right G}) : Prop :=
  forall x y, x \in ZL -> y \in ZR -> @x94_biedge G x y.

Definition x94_anticomplete_pair
    (G : x94_bigraph) (ZL : {set x94_left G}) (ZR : {set x94_right G}) : Prop :=
  forall x y, x \in ZL -> y \in ZR -> ~~ @x94_biedge G x y.

Definition x94_pure_pair
    (G : x94_bigraph) (ZL : {set x94_left G}) (ZR : {set x94_right G}) : Prop :=
  @x94_complete_pair G ZL ZR \/ @x94_anticomplete_pair G ZL ZR.

(** ** X94 statements ******************************************************)

(** Studies slice: Bipartite strong Erdos-Hajnal conjecture for forest
    bigraphs and their bicomplements, with the linear pure-pair threshold
    written as a positive rational epsilon. *)
Definition bipartite_strong_erdos_hajnal_forest_bigraph_statement : Prop :=
  forall H : x94_bigraph,
    @x94_forest_bigraph H ->
    exists eps_num eps_den : nat,
      [/\ 0 < eps_num, 0 < eps_den
        & forall G : x94_bigraph,
            @x94_H_free G H ->
            @x94_H_free G (@x94_bicomplement H) ->
            exists (ZL : {set x94_left G}) (ZR : {set x94_right G}),
              [/\ @x94_pure_pair G ZL ZR,
                  eps_num * #|x94_left G| <= eps_den * #|ZL|
                & eps_num * #|x94_right G| <= eps_den * #|ZR|]].
