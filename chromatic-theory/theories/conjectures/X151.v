(** * Chromatic.conjectures.X151 -- v2 random chromatic concentration row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X151 vocabulary ***********************************************)

Definition x151_chi_in_interval
    (n c start : nat) (E : {set {set 'I_n}}) : bool :=
  let G := fg_labelled_sgraph E in
  (start <= χ([set: G])) && (χ([set: G]) <= start + c).

Definition x151_not_constant_concentrated (p q c : nat) : Prop :=
  exists a b : nat,
    [/\ 0 < a, a <= b &
      eventually (fun n =>
        forall start : nat,
          b * @fg_event_weight {set {set 'I_n}} (@fg_gnp_weight p q n)
                (fun E => x151_chi_in_interval c start E) <=
          (b - a) * @fg_total_weight {set {set 'I_n}} (@fg_gnp_weight p q n))].

(** ** X151 statements *****************************************************)

(** The extracted open problem asks for a lower bound ruling out concentration of
    chi(G(n,p)), for fixed p, in a constant-length interval.  Here [p/q] is a
    fixed rational edge probability, and concentration is negated by an eventual
    probability gap from one for every interval of length [c]. *)
Definition random_graph_chromatic_not_constant_concentrated_statement : Prop :=
  forall p q : nat,
    0 < p ->
    p < q ->
    forall c : nat,
      x151_not_constant_concentrated p q c.
