(** * GTMisc.conjectures.X141 -- v2 zero-forcing Cartesian product row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X141 vocabulary ***********************************************)

(** Zero-forcing closure: from a blue set [S], a blue vertex [u] may force the
    unique uncoloured neighbour [v] when [N(u) \ S] is exactly [{v}]. *)
Inductive x141_zf_closure (G : sgraph) : {set G} -> {set G} -> Prop :=
| x141_zf_done (S : {set G}) : @x141_zf_closure G S S
| x141_zf_step (S T : {set G}) (u v : G) :
    u \in S ->
    v \notin S ->
    N(u) :\: S = [set v] ->
    @x141_zf_closure G (S :|: [set v]) T ->
    @x141_zf_closure G S T.

Definition x141_zero_forcing_set (G : sgraph) (S : {set G}) : Prop :=
  @x141_zf_closure G S [set: G].

Definition x141_zero_forcing_number_le (G : sgraph) (k : nat) : Prop :=
  exists S : {set G}, #|S| <= k /\ x141_zero_forcing_set S.

Definition x141_zero_forcing_number (G : sgraph) (z : nat) : Prop :=
  x141_zero_forcing_number_le G z /\
  forall k : nat, x141_zero_forcing_number_le G k -> z <= k.

(** ** X141 statements *****************************************************)

(** Fitzpatrick-Howell-Messinger-Pike: the zero forcing number is subadditive
    under Cartesian product, z(G square H) <= z(G)+z(H). *)
Definition zero_forcing_cartesian_product_subadditivity_statement : Prop :=
  forall (G H : sgraph) (zG zH : nat),
    x141_zero_forcing_number G zG ->
    x141_zero_forcing_number H zH ->
    x141_zero_forcing_number_le (cartesian_product G H) (zG + zH).
