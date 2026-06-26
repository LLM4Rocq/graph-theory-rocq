(** * Digraph.digraph — directed graphs as a Hierarchy-Builder structure

    DESIGN (docs/DESIGN.md §2 principle 2, Decision D7): graph-theory models
    its [diGraph] as a plain telescope record, which cannot host HB mixins.
    We therefore root our own hierarchy here —

      [HasArc] (a bare arc relation, no finiteness: the D4 seam)
        --> [RelDigraph]            relation-level digraphs
        --> [DiGraph]               finite digraphs ([diGraphType])
        --> [Tournament]            (core/tournament.v)

    — and consume graph-theory through explicit projections into their record
    world ([to_GT] below; the backedge [sgraph] in core/order.v). All glue
    with graph-theory's records lives in this file, core/order.v and the
    interop file, so any coercion friction stays localised.

    Sub-digraphs are declared as canonical instances on subtypes
    [{x : D | P x}] (mirroring how mathcomp equips [sig] with [Finite]), so
    *every* sig over a digraph is itself a digraph with the induced arcs —
    no ad-hoc wrapper types needed. *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude.
From Digraph Require Import interop_graph_theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** The hierarchy *)

(** A bare arc relation on an arbitrary carrier — the infinite-vertex seam
    (D4) keeps this layer finiteness-free. *)
HB.mixin Record HasArc V := { arc : rel V }.

#[short(type="relDigraph")]
HB.structure Definition RelDigraph := { V of HasArc V }.

(** Finite digraphs: the workhorse for everything tournament-related. *)
#[short(type="diGraphType")]
HB.structure Definition DiGraph := { V of HasArc V & Finite V }.

Declare Scope digraph_scope.
Delimit Scope digraph_scope with dg.
Open Scope digraph_scope.

Notation "u --> v" := (arc u v) (at level 30) : digraph_scope.

(** ** Projection into graph-theory's record world (D7 glue)

    [diGraph] is graph-theory's notation for its [relType] record
    (re-exported by the interop file); [RelType] is its constructor — its
    [DiGraph] alias is shadowed by our structure module above. *)

Definition to_GT (D : diGraphType) : diGraph := RelType (@arc D).

(** ** Converse digraph (type alias, mathcomp [T^d]-style) *)

Definition converse (D : diGraphType) : Type := D.

HB.instance Definition _ (D : diGraphType) := Finite.on (converse D).
HB.instance Definition _ (D : diGraphType) :=
  HasArc.Build (converse D) (fun u v : D => arc v u).

Lemma converse_arcE (D : diGraphType) (u v : D) :
  ((u : converse D) --> (v : converse D)) = (v --> u).
Proof. by []. Qed.

(** ** Sub-digraphs: subtypes are canonically digraphs *)

Section SubDigraph.
Variables (D : diGraphType) (P : pred D).

HB.instance Definition _ :=
  HasArc.Build {x | P x} (fun u v : {x | P x} => arc (val u) (val v)).

Lemma sub_arcE (u v : {x | P x}) : (u --> v) = (val u --> val v).
Proof. by []. Qed.

End SubDigraph.

(** Object-level versions, convenient in statements (the [: diGraphType]
    cast goes through Rocq's reverse-coercion via the canonical instances). *)

Definition induced_digraph (D : diGraphType) (S : {set D}) : diGraphType :=
  {x : D | x \in S} : diGraphType.

Definition del_vertex (D : diGraphType) (v : D) : diGraphType :=
  induced_digraph [set~ v].

(** ** Digraph isomorphism

    (Named [dgiso]: graph-theory's [diso] — re-exported through the interop —
    is the *simple-graph* isomorphism.) *)

Definition dgiso (D1 D2 : diGraphType) : Prop :=
  exists f : D1 -> D2, bijective f /\ forall u v, (f u --> f v) = (u --> v).

Lemma dgiso_refl (D : diGraphType) : dgiso D D.
Proof. by exists id; split=> //; exists id. Qed.

Lemma dgiso_sym (D1 D2 : diGraphType) : dgiso D1 D2 -> dgiso D2 D1.
Proof.
case=> f [[g fK gK] arcE]; exists g; split; first by exists f.
by move=> u v; rewrite -{2}[u]gK -{2}[v]gK arcE.
Qed.

Lemma dgiso_trans (D1 D2 D3 : diGraphType) :
  dgiso D1 D2 -> dgiso D2 D3 -> dgiso D1 D3.
Proof.
case=> f [bij_f arcEf] [g [bij_g arcEg]]; exists (g \o f).
split; first exact: bij_comp.
by move=> u v /=; rewrite arcEg arcEf.
Qed.

Lemma dgiso_card (D1 D2 : diGraphType) : dgiso D1 D2 -> #|D1| = #|D2|.
Proof. by case=> f [/bij_eq_card-> _]. Qed.
