(** * Topological.foundations.crossing — combinatorial split-planarization proxy

    AREA-LOCAL foundation for milestone D3cr (crossing-number conjectures).  We
    define a crossing-number proxy WITHOUT any geometry / drawings / surfaces /
    faces / point-sets, via a PLANARIZATION-style split model built on base's
    combinatorial planarity [wagner_planar] (Wagner: no K5 / K3,3 minor).

    PLANARIZATION.  A single "crossing resolution" of a drawing turns one crossing
    point of two independent (vertex-disjoint) edges [a-b], [c-d] into a degree-4
    vertex [x] adjacent to [a,b,c,d], with the two crossed edges removed.  This is
    exactly [xsplit G a b c d] below (carrier [option G], the new vertex [None]).
    A drawing of [G] with [k] crossings then corresponds to a chain of [k] such
    resolutions ending in a PLANAR graph (its planarization); an edge crossed
    several times is split several times, in sequence.  Hence:

      [crossing_planar_in k G]  :  G can be resolved by EXACTLY k crossing
                                    splits into a [wagner_planar] graph;
      [is_crossing_number G n]  :  n is the LEAST such k in this split model.

    This is the split-planarization model used by the D3 statements.  It is
    axiom-free and grounded, but the #5/#6 readback review flagged one missing
    correspondence ingredient for equality with the usual drawing crossing
    number: local rotation/alternation data at each new degree-4 crossing vertex.
    Until that drawing/rotation equivalence layer is built, downstream
    crossing-number rows are recorded as PARTIAL proxy statements.

    WHY RELATIONAL (not a total [crossing_number : sgraph -> nat]).  Totality of
    a [nat]-valued [cr] needs the fact "every finite graph has a finite crossing
    number", i.e. admits SOME finite-crossing drawing.  The only known proofs go
    through an actual drawing (e.g. a rectilinear / straight-line layout), i.e.
    GEOMETRY — which this combinatorial layer deliberately excludes, and which we
    must not introduce via an [Axiom] (the file is axiom-free).  We therefore
    expose the relational least-[k] predicate [is_crossing_number]
    (functional: at most one [n] satisfies it), which is all the conjecture
    statements need.

    GROUNDING (a fake/trivial cr would FAIL these):
      - [crossing_number0]      : is_crossing_number G 0 <-> wagner_planar G  (both ways);
      - [wagner_planar_sub]     : planarity is subgraph-closed — the BASE CASE of
                                  crossing-number monotonicity under the subgraph
                                  relation (see the honest note on the full
                                  inductive statement below);
      - [is_crossing_number_K5] : ~ wagner_planar 'K_5, hence cr('K_5) >= 1
                                  (is_crossing_number 'K_5 n -> 0 < n). *)

From GTBase Require Export base.
From GraphTheory Require Import minor.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Doubleton commutativity helper (the unordered edge {u,v}). *)
Lemma set2C (T : finType) (a b : T) : [set a; b] = [set b; a].
Proof. by apply/setP=> z; rewrite !inE orbC. Qed.

Section Xsplit.
Variable G : sgraph.

(** [{u,v}] equals the edge [{a,b}] (unordered). *)
Definition same_edge (u v a b : G) : bool := [set u; v] == [set a; b].

(** The adjacency of [xsplit G a b c d]: vertices are [option G] (the new
    crossing vertex is [None]); the edges [a-b] and [c-d] are deleted and the new
    vertex is joined to [a,b,c,d]. *)
Definition xsplit_rel (a b c d : G) : rel (option G) :=
  fun p q =>
    match p, q with
    | Some u, Some v =>
        (u -- v) && ~~ same_edge u v a b && ~~ same_edge u v c d
    | Some u, None | None, Some u => (u == a) || (u == b) || (u == c) || (u == d)
    | None, None => false
    end.

Lemma xsplit_sym (a b c d : G) : symmetric (xsplit_rel a b c d).
Proof.
move=> [u|] [v|] //=.
by rewrite sgP /same_edge (set2C v u).
Qed.

Lemma xsplit_irrefl (a b c d : G) : irreflexive (xsplit_rel a b c d).
Proof. by move=> [u|] //=; rewrite sgP. Qed.

Definition xsplit (a b c d : G) : sgraph :=
  SGraph (@xsplit_sym a b c d) (@xsplit_irrefl a b c d).

End Xsplit.

(** [crossing_planar_in k G]: G is planarized by EXACTLY [k] crossing splits.
    Each split resolves a crossing of two vertex-disjoint edges (the [uniq]
    guard makes [a,b,c,d] four distinct vertices ⇒ the two edges are
    independent). *)
Fixpoint crossing_planar_in (k : nat) (G : sgraph) {struct k} : Prop :=
  match k with
  | 0 => wagner_planar G
  | k'.+1 =>
      exists (a b c d : G),
        [/\ a -- b, c -- d & uniq [:: a; b; c; d]]
        /\ crossing_planar_in k' (xsplit a b c d)
  end.

(** Split-crossing value n: the least number of crossing splits planarizing G. *)
Definition is_crossing_number (G : sgraph) (n : nat) : Prop :=
  crossing_planar_in n G /\ (forall k, crossing_planar_in k G -> n <= k).

(** [is_crossing_number] is FUNCTIONAL: the split value is unique when it exists. *)
Lemma is_crossing_number_uniq (G : sgraph) (m n : nat) :
  is_crossing_number G m -> is_crossing_number G n -> m = n.
Proof.
move=> [Pm Lm] [Pn Ln]; apply/eqP; rewrite eqn_leq.
by rewrite (Lm _ Pn) (Ln _ Pm).
Qed.

(** ** Grounding 1 — split-cr(G) = 0 iff G is (combinatorially) planar. *)
Lemma crossing_number0 (G : sgraph) :
  is_crossing_number G 0 <-> wagner_planar G.
Proof.
split=> [[H0 _]|H]; first exact: H0.
by split=> // k _; apply: leq0n.
Qed.

(** ** Grounding 2 (base case) — planarity is subgraph-closed.

    This is the BASE CASE (k = 0) of the full monotonicity of split-cr under the
    subgraph relation, [subgraph H G -> split-cr(H) <= split-cr(G)].  The full inductive
    statement holds mathematically (delete from a planarization of G everything
    not in H, smoothing the freed crossing vertices), but its combinatorial proof
    in this model requires a crossing-vertex "smoothing/commutation" development
    that is out of scope for this statement milestone; it is NOT asserted as an
    axiom here.  The base case below is what grounds cr's planar floor. *)
Lemma wagner_planar_sub (H G : sgraph) :
  subgraph H G -> wagner_planar G -> wagner_planar H.
Proof.
move=> sub [n5 n33]; have mGH : minor G H by apply: sub_minor.
by split=> hm; [apply: n5 | apply: n33]; apply: minor_trans mGH hm.
Qed.

(** ** Grounding 3 — K5 is not planar, so cr(K5) >= 1. *)
Lemma not_wagner_planar_K5 : ~ wagner_planar 'K_5.
Proof.
case=> n5 _; apply: n5.
apply: (minor_of_clique (S := [set: 'K_5]) (n := 5)); last exact: Kn_clique.
by rewrite cardsT card_ord.
Qed.

Lemma is_crossing_number_K5 (n : nat) : is_crossing_number 'K_5 n -> 0 < n.
Proof.
case: n => [|n] // [H0 _].
by case: not_wagner_planar_K5; apply: H0.
Qed.
