(** * Digraph.automorphism — automorphism group, vertex-transitivity

    Aut(D) is the set of permutations of the (finite) vertex set that
    preserve the arc relation; it is a group under composition. A digraph is
    vertex-transitive when Aut(D) acts transitively on vertices.

    This layer is deliberately thin (docs/DESIGN.md §1): mathcomp's
    [{perm V}]/[fingroup] provide all group machinery; we only add the
    graph-specific predicate. The M3 result "vertex-transitive ⇒ ω̄(T − v)
    independent of v" builds on this (invariants_advanced/transitive.v). *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_fingroup all_algebra.
From Digraph Require Import prelude digraph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Automorphism.
Variable D : diGraphType.
Implicit Types (p q : {perm D}) (u v : D).

(** [p] is an automorphism: it preserves arcs (hence also non-arcs). *)
Definition autb p : bool :=
  [forall u : D, [forall v : D, arc (p u) (p v) == arc u v]].

Lemma autbP p : reflect (forall u v, ((p u) --> (p v)) = (u --> v)) (autb p).
Proof.
apply: (iffP idP) => [h u v|h].
- by have /forallP/(_ u)/forallP/(_ v)/eqP := h.
- by apply/forallP=> u; apply/forallP=> v; rewrite h.
Qed.

Definition dgaut : {set {perm D}} := [set p | autb p].

Lemma dgautE p : (p \in dgaut) = autb p.
Proof. by rewrite inE. Qed.

Lemma dgaut1 : 1%g \in dgaut.
Proof. by rewrite inE; apply/autbP=> u v; rewrite !perm1. Qed.

Lemma dgautM : {in dgaut &, forall p q, (p * q)%g \in dgaut}.
Proof.
move=> p q; rewrite !inE => /autbP hp /autbP hq.
by apply/autbP=> u v; rewrite !permM hq hp.
Qed.

Lemma dgaut_group_set : group_set dgaut.
Proof. by apply/group_setP; split; [exact: dgaut1 | exact: dgautM]. Qed.

Canonical dgaut_group : {group {perm D}} := Group dgaut_group_set.

(** Vertex-transitivity. *)
Definition vertex_transitiveb : bool :=
  [forall u : D, [forall v : D,
    [exists p : {perm D}, (p \in dgaut) && (p u == v)]]].

Lemma vertex_transitivebP :
  reflect (forall u v, exists2 p, p \in dgaut & p u = v) vertex_transitiveb.
Proof.
apply: (iffP idP) => [h u v|h].
- have /forallP/(_ u)/forallP/(_ v)/existsP[p /andP[paut /eqP pe]] := h.
  by exists p.
- apply/forallP=> u; apply/forallP=> v; apply/existsP.
  by have [p paut pe] := h u v; exists p; rewrite paut pe eqxx.
Qed.

End Automorphism.
