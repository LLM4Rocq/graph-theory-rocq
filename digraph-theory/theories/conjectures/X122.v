(** * Digraph.conjectures.X122 -- v2 dijoin inversion-number additivity row *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph.
From Digraph.conjectures Require Import X92.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X122 vocabulary ************************************************)

(** Oriented = loopless and digon-free (asymmetric arc relation): identical to
    [chi_bounded.oriented_dg] / the [X2.x2_oriented] guard.  It forbids loops,
    since [u --> u -> ~~ (u --> u)] is contradictory, and antiparallel pairs. *)
Definition x122_oriented (D : diGraphType) : Prop :=
  forall u v : D, u --> v -> ~~ (v --> u).

(** The dijoin [L -> R]: the disjoint union of [L] and [R] on the sum type
    [V(L) + V(R)] with, in addition to the arcs of [L] and of [R], every arc
    directed from [L] to [R] (complete domination L ⇒ R and no arc R -> L).
    Same sum-type construction as [heroes.djoin] / [X2.x2_disjoint_union]. *)
Section Dijoin.
Variables L R : diGraphType.

Definition x122_dijoin : Type := (L + R)%type.
HB.instance Definition _ := Finite.on x122_dijoin.

Definition x122_dijoin_rel (x y : L + R) : bool :=
  match x, y with
  | inl a, inl b => a --> b
  | inr a, inr b => a --> b
  | inl _, inr _ => true
  | inr _, inl _ => false
  end.

HB.instance Definition _ := HasArc.Build x122_dijoin x122_dijoin_rel.
End Dijoin.

(** The inversion number of a digraph (Bang-Jensen–da Silva–Havet): the least
    number of subset-inversions needed to make it acyclic, where one inversion
    picks a vertex subset and reverses every arc with both ends in it.  We REUSE
    X92's inversion apparatus [x92_inverts_to_acyclic] (a [steps : seq {set D}]
    applies the successive subset-inversions and yields an acyclic relation) and
    express "[inv D = k]" as: some length-[k] sequence makes [D] acyclic AND no
    sequence shorter than [k] does.  This pins [k] to the minimum without a
    finiteness proof, and holds of exactly one [k] whenever [D] can be made
    acyclic at all (which every oriented [D] can).  Cf. X92.v. *)
Definition x122_inv_eq (D : diGraphType) (k : nat) : Prop :=
  (exists steps : seq {set D},
     size steps = k /\ @x92_inverts_to_acyclic D steps) /\
  (forall steps : seq {set D},
     @x92_inverts_to_acyclic D steps -> k <= size steps).

(** ** X122 statements ******************************************************)

(** Bang-Jensen–da Silva–Havet "Dijoin conjecture": for oriented graphs [L] and
    [R], inv(L -> R) = inv(L) + inv(R).  Encoded relationally: whenever
    inv(L) = kL and inv(R) = kR (each pinned uniquely by [x122_inv_eq]), the
    dijoin [L -> R] has inversion number kL + kR.  (The dijoin of two oriented
    graphs is oriented — cross-arcs go only L -> R — so its inversion number is
    well-defined, i.e. [x122_inv_eq (x122_dijoin L R)] is satisfiable.) *)
Definition dijoin_inversion_number_additive_statement : Prop :=
  forall (L R : diGraphType) (kL kR : nat),
    x122_oriented L -> x122_oriented R ->
    x122_inv_eq L kL -> x122_inv_eq R kR ->
    x122_inv_eq (x122_dijoin L R) (kL + kR).
