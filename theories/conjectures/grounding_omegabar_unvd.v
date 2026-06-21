(** * Digraph.conjectures.grounding_omegabar_unvd — grounding the ω̄ / unvd cluster

    Solo grounding pass (the round-3 agent for this cluster stalled on transient API
    rate-limiting before writing a file).  Grounds:
      - [contains_subdigraph] is a PREORDER (reflexive + transitive) — the unvd containment
        relation is a genuine order, as its meaning requires;
      - ω̄ DISCRIMINATES: ω̄(TTₙ) = 1 < 2 = ω̄(C₃) (so ω̄ is not constant/degenerate);
      - the domination/ω̄ tie on C₃: domnum(C₃) ≤ ω̄(C₃) = 2 (instantiating
        [domnum_le_omegabar]).
    The flagship circulant value ω̄(ACₘ) = 3 ([omegabar_AC], acn_base.v) is already grounded
    transitively via [grounding_clique_long.gr_conj_5_10_nonvacuous] (the 5.10 non-vacuity
    witnesses use the AC families), so it is not re-derived here. *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph oriented tournament.
From Digraph Require Import omegabar critical domination.
From Digraph Require Import unvd.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** [contains_subdigraph] is a preorder

    [contains_subdigraph H D] := an injection [H -> D] preserving arcs.  The unvd number
    is "least N such that every N-vertex tournament contains [D]", so containment must be
    reflexive (every digraph contains itself) and transitive (containment chains compose).
    Both hold; the witnesses are [id] and function composition. *)
Lemma gr_contains_refl (D : diGraphType) : contains_subdigraph D D.
Proof. by exists id; split=> // u v. Qed.

Lemma gr_contains_trans (A B C : diGraphType) :
  contains_subdigraph A B -> contains_subdigraph B C -> contains_subdigraph A C.
Proof.
move=> [f [finj farc]] [g [ginj garc]].
exists (g \o f); split; first exact: inj_comp ginj finj.
by move=> u v /farc/garc.
Qed.

(** ** ω̄ discriminates between the transitive tournament and the directed triangle

    ω̄(TTₙ) = 1 (a transitive tournament has an acyclic order with no back-edge clique) and
    ω̄(C₃) = 2.  So the backedge-clique invariant is non-degenerate (it separates the
    smallest non-transitive tournament from the transitive ones). *)
Lemma gr_omegabar_TT_lt_C3 (n : nat) :
  0 < n -> (ω̄((TT n : tournament)) < ω̄((C3 : tournament)))%N.
Proof. by move=> n0; rewrite omegabar_TT // omegabar_C3. Qed.

(** ** Domination number ≤ ω̄, concretely on C₃

    [domnum_le_omegabar] gives domnum(T) ≤ ω̄(T) for every tournament; on C₃ this is
    domnum(C₃) ≤ 2.  Grounds the [conj_5_8 ⟹ dom-cluster] edge's underlying inequality on a
    concrete witness. *)
Lemma gr_domnum_C3_le2 : (domnum (C3 : tournament) <= 2)%N.
Proof. by rewrite -omegabar_C3; exact: domnum_le_omegabar. Qed.
