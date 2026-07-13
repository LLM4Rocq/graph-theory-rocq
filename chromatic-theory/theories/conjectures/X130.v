(** * Chromatic.conjectures.X130 -- v2 planar girth-5 fractional-chromatic row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X130 vocabulary ************************************************)

(** An (a:b)-fold colouring of G: every vertex receives a b-element subset of an
    a-element palette ['I_a], and adjacent vertices receive DISJOINT subsets.
    (This replicates base/Extremal's [bfold_colouring]; the fractional chromatic
    number χ_f(G) = inf a/b over all such colourings, attained/rational for a
    finite G.) *)
Definition x130_bfold_colouring (G : sgraph) (a b : nat) (f : G -> {set 'I_a}) : Prop :=
  (forall v : G, #|f v| = b) /\ (forall x y : G, x -- y -> [disjoint f x & f y]).

(** [x130_frac_chi_le G p q]: the fractional chromatic number of G is ≤ p/q.
    Since χ_f(G) is the infimum of a/b over (a:b)-colourings and this infimum is
    ATTAINED for a finite graph, "χ_f(G) ≤ p/q" is equivalent to the EXISTENCE of
    an (a:b)-colouring with a/b ≤ p/q, i.e. a·q ≤ p·b (cross-multiplied, q>0).
    Soundness holds unconditionally: any such colouring witnesses χ_f(G) ≤ a/b ≤
    p/q; the converse uses attainment (a genuine theorem for finite graphs). *)
Definition x130_frac_chi_le (G : sgraph) (p q : nat) : Prop :=
  exists (a b : nat) (f : G -> {set 'I_a}),
    [/\ (0 < b)%N, @x130_bfold_colouring G a b f & (a * q <= p * b)%N].

(** ** X130 statements ******************************************************)

(** Dvořák–Mnich: there is a real number c < 3 such that every planar graph of
    girth at least 5 has fractional chromatic number at most c.

    Faithfulness. The fractional chromatic number of a finite graph is RATIONAL,
    and the conjecture asserts a UNIFORM bound strictly below 3; hence "∃ real
    c < 3" is faithfully captured by "∃ rational p/q < 3" (encoded [0 < q] and
    [p < 3q]) — a single bound in the correct ∃(p,q),∀G order (a per-graph bound
    would be trivially true and wrong). "girth at least 5" is [girth_geq G 5]
    (girth ≥ 5), not [has_girth] (girth exactly 5). Non-vacuity: [p = 0] cannot
    satisfy the existential, since [x130_frac_chi_le G 0 q] would force a·q ≤ 0,
    i.e. a 0-colour palette, impossible for a nonempty graph; so no degenerate
    (p,q) witness exists and the statement is the genuine open problem. *)
Definition dvorak_mnich_planar_girth5_fractional_chromatic_statement : Prop :=
  exists p q : nat,
    [/\ (0 < q)%N, (p < 3 * q)%N &
      forall G : sgraph,
        wagner_planar G ->
        girth_geq G 5 ->
        x130_frac_chi_le G p q].
