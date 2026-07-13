(** * Hypergraph.conjectures.X117 -- v2 hedgehog Ramsey row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X117 vocabulary ***********************************************)

(** *** The hedgehog H_t as a concrete finite 3-uniform hypergraph.

    Body: [t] vertices, [inl i] for [i : 'I_t].
    Spikes: one distinct vertex [inr s] for every ordered pair [s = (i,j)]
    with [i < j], i.e. exactly [C(t,2)] spikes -- one per unordered pair.
    Hyperedges: [{inl i, inl j, inr s}] for each spike [s = (i,j)].  Each
    spike lies in exactly one edge, each edge has 3 distinct vertices, so
    [H_t] is 3-uniform with body [t] and [C(t,2)] spikes/edges. *)

Definition x117_spike (t : nat) : Type := {p : 'I_t * 'I_t | p.1 < p.2}.

Definition x117_vertex (t : nat) : Type := ('I_t + x117_spike t)%type.

Definition x117_edge (t : nat) (s : x117_spike t) : {set x117_vertex t} :=
  [set inl (sval s).1; inl (sval s).2; inr s].

Definition x117_edges (t : nat) : {set {set x117_vertex t}} :=
  [set x117_edge s | s : x117_spike t].

(** *** Two-colour monochromatic copy in the complete 3-uniform host. *)

Definition x117_image_edge
    (T : finType) (N : nat) (f : T -> 'I_N) (e : {set T}) : {set 'I_N} :=
  [set y : 'I_N | [exists x : T, (x \in e) && (y == f x)]].

Definition x117_monochromatic_copy
    (T : finType) (E : {set {set T}}) (N : nat)
    (col : {set 'I_N} -> bool) : Prop :=
  exists (colour : bool) (f : T -> 'I_N),
    injective f /\
    forall e : {set T},
      e \in E -> col (x117_image_edge f e) = colour.

(** [N] vertices force a monochromatic copy under every 2-colouring of the
    3-subsets of the host. *)
Definition x117_forces_mono
    (T : finType) (E : {set {set T}}) (N : nat) : Prop :=
  forall col : {set 'I_N} -> bool, x117_monochromatic_copy E col.

(** [R] is the two-colour Ramsey number [r(H_t;2)]: the least host size that
    forces a monochromatic copy of [H_t]. *)
Definition x117_ramsey_number (t R : nat) : Prop :=
  x117_forces_mono (x117_edges t) R /\
  forall N : nat, x117_forces_mono (x117_edges t) N -> R <= N.

(** ** X117 statements *****************************************************)

(** Conlon-Fox-Rodl.  Question: is [r(H_t;2) = t^{2+o(1)}]?  Here [H_t] is
    the hedgehog above.  We encode "[= t^{2+o(1)}]" two-sidedly: for every
    rational [eps = e1/e2 > 0] there is a threshold [t0] such that for all
    [t >= t0], [t^{2-eps} <= r(H_t;2) <= t^{2+eps}].  The exponents are made
    integral by raising to the power [e2] and cross-multiplying:
    [t^{2-eps} <= R  <->  t^{2 e2 - e1} <= R^{e2}] and
    [R <= t^{2+eps}  <->  R^{e2} <= t^{2 e2 + e1}].
    (Truncated nat subtraction only weakens the lower bound for [eps >= 2],
    where it is already implied; the binding content is at small [eps].) *)
Definition conlon_fox_rodl_hedgehog_ramsey_statement : Prop :=
  forall e1 e2 : nat,
    0 < e1 -> 0 < e2 ->
    exists t0 : nat,
      forall t R : nat,
        t0 <= t ->
        x117_ramsey_number t R ->
        t ^ (2 * e2 - e1) <= R ^ e2 /\ R ^ e2 <= t ^ (2 * e2 + e1).
