(** * Hypergraph.conjectures.X119 -- v2 3-uniform Ramsey tower row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X119 vocabulary ***********************************************)

Definition x119_uniform (T : finType) (E : {set {set T}}) (r : nat) : Prop :=
  forall e : {set T}, e \in E -> #|e| = r.

(** No isolated vertices: every vertex of the ground type lies in some edge. *)
Definition x119_no_isolated (T : finType) (E : {set {set T}}) : Prop :=
  forall v : T, exists e : {set T}, e \in E /\ v \in e.

(** *** q-colour monochromatic copy in the complete 3-uniform host. *)

Definition x119_image_edge
    (T : finType) (N : nat) (f : T -> 'I_N) (e : {set T}) : {set 'I_N} :=
  [set y : 'I_N | [exists x : T, (x \in e) && (y == f x)]].

Definition x119_monochromatic_copy
    (T : finType) (E : {set {set T}}) (N q : nat)
    (col : {set 'I_N} -> 'I_q) : Prop :=
  exists (colour : 'I_q) (f : T -> 'I_N),
    injective f /\
    forall e : {set T},
      e \in E -> col (x119_image_edge f e) = colour.

(** [N] vertices force a monochromatic copy under every [q]-colouring of the
    3-subsets of the host. *)
Definition x119_forces_mono
    (T : finType) (E : {set {set T}}) (q N : nat) : Prop :=
  forall col : {set 'I_N} -> 'I_q, x119_monochromatic_copy E col.

(** [R] is the [q]-colour 3-uniform Ramsey number [r_3(H;q)]: the least host
    size forcing a monochromatic copy of [H = (T,E)]. *)
Definition x119_ramsey_number
    (T : finType) (E : {set {set T}}) (q R : nat) : Prop :=
  x119_forces_mono E q R /\
  forall N : nat, x119_forces_mono E q N -> R <= N.

(** Integer ceiling square root: the least [s] with [m <= s^2].  Chosen as an
    upper approximation of [sqrt m] so the tower bound stays an honest upper
    bound; the outer existential [cq] absorbs the O(1) rounding factor. *)
Lemma x119_sqrt_ex (m : nat) : exists s : nat, m <= s ^ 2.
Proof. exists m. by rewrite expnS expn1; case: m => // n; rewrite leq_pmulr. Qed.

Definition x119_sqrt (m : nat) : nat := ex_minn (x119_sqrt_ex m).

(** ** X119 statements *****************************************************)

(** Conlon-Fox-Sudakov.  For every number of colours [q >= 2] there is a
    constant [c_q] such that every 3-uniform hypergraph [H] with [m] edges
    and no isolated vertices has [q]-colour Ramsey number
    [r_3(H;q) <= 2^(2^(c_q * sqrt m))].  The constant [c_q] depends on [q]
    only (existential placed after [forall q]); [m = #|E|] is the number of
    edges; [sqrt m] is the ceiling square root [x119_sqrt]. *)
Definition conlon_fox_sudakov_three_uniform_ramsey_tower_statement : Prop :=
  forall q : nat,
    2 <= q ->
    exists cq : nat,
      forall (T : finType) (E : {set {set T}}),
        x119_uniform E 3 ->
        x119_no_isolated E ->
        forall R : nat,
          x119_ramsey_number E q R ->
          R <= 2 ^ (2 ^ (cq * x119_sqrt #|E|)).
