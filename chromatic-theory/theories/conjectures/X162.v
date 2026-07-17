(** * Chromatic.conjectures.X162 -- v2 WSK triangular-lattice Kempe row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X162 vocabulary ***********************************************)

Definition x162_tri_rel (m n : nat) : rel ('I_m * 'I_n) :=
  fun p q =>
    [|| ((val p.1).+1 %% m == val q.1) && (p.2 == q.2),
        (p.1 == q.1) && ((val p.2).+1 %% n == val q.2)
      | ((val p.1).+1 %% m == val q.1) &&
        ((val p.2 + n.-1) %% n == val q.2)].

Definition x162_periodic_triangular_lattice (m n : nat) : sgraph :=
  @fg_mk_sgraph ('I_m * 'I_n)%type (@x162_tri_rel m n).

Definition x162_proper_colouring (G : sgraph) (q : nat) (col : G -> 'I_q) : Prop :=
  forall x y : G, x -- y -> col x != col y.

Definition x162_uses_only_two_colours
    (G : sgraph) (q : nat) (col : G -> 'I_q) (a b : 'I_q) (S : {set G}) : Prop :=
  forall v : G, v \in S -> (col v == a) || (col v == b).

Definition x162_swap_colour (q : nat) (a b c : 'I_q) : 'I_q :=
  if c == a then b else if c == b then a else c.

Definition x162_kempe_step (G : sgraph) (q : nat) (col col' : G -> 'I_q) : Prop :=
  exists (a b : 'I_q) (S : {set G}),
    [/\ a != b,
        connected S,
        x162_uses_only_two_colours col a b S &
        forall v : G,
          col' v = if v \in S then x162_swap_colour a b (col v) else col v].

Inductive x162_kempe_reachable
    (G : sgraph) (q : nat) : (G -> 'I_q) -> (G -> 'I_q) -> Prop :=
| x162_kempe_refl col : @x162_kempe_reachable G q col col
| x162_kempe_trans col1 col2 col3 :
    @x162_kempe_step G q col1 col2 ->
    @x162_kempe_reachable G q col2 col3 ->
    @x162_kempe_reachable G q col1 col3.

Definition x162_kempe_class_for_q (G : sgraph) (q : nat) : Prop :=
  forall col1 col2 : G -> 'I_q,
    x162_proper_colouring col1 ->
    x162_proper_colouring col2 ->
    @x162_kempe_reachable G q col1 col2.

(** ** X162 statements *****************************************************)

(** Open case: validity of the WSK algorithm for q=5 colourings of the periodic
    triangular lattice, equivalently whether the 5-colourings form one Kempe
    class under two-colour component swaps. *)
Definition wsk_triangular_lattice_q5_kempe_class_statement : Prop :=
  forall m n : nat,
    0 < m -> 0 < n ->
    x162_kempe_class_for_q (x162_periodic_triangular_lattice m n) 5.
