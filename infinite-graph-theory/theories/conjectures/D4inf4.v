(** * Infinite.conjectures.D4inf4 — two sibling carriers.

    - strong_matchings_and_covers (done): a possibly-infinite HYPERGRAPH
      [iHypergraph] (vertices, edges, incidence); "strongly maximal / minimal"
      uses [card_le] (the choice-free injection form of the symmetric-difference
      cardinal comparison).
    - universal_highly_arc_transitive_digraphs (done): a DIGRAPH [iDigraph]
      (irreflexive, NON-symmetric arc relation).  "Highly arc transitive" is the
      transitive automorphism ACTION written out (an adjacency-preserving
      bijection sending any directed path to any equal-length one) — never a
      constructed automorphism GROUP object.  "Universal" is the source's
      alternating-walk condition. *)

From GTBase Require Export base.
From Infinite Require Import foundations.igraph.
From mathcomp Require Import all_boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ================================================================= *)
(** ** strong_matchings_and_covers  (Conjecture, OPEN) *)

Record iHypergraph := Build_iHypergraph {
  hV : Type;
  hE : Type;
  hinc : hE -> hV -> Prop }.

(** Edge [e] has size ≤ [k]: its vertices are covered by ['I_k]. *)
Definition hedge_le (H : iHypergraph) (k : nat) (e : hE H) : Prop :=
  exists g : 'I_k -> hV H, forall v, hinc e v -> exists i, g i = v.

(** A MATCHING: pairwise vertex-disjoint edges. *)
Definition hmatching (H : iHypergraph) (F : hE H -> Prop) : Prop :=
  forall e1 e2, F e1 -> F e2 -> (exists v, hinc e1 v /\ hinc e2 v) -> e1 = e2.

(** A (vertex) COVER: every edge contains a chosen vertex. *)
Definition hcover (H : iHypergraph) (X : hV H -> Prop) : Prop :=
  forall e : hE H, exists v, X v /\ hinc e v.

(** [F] is STRONGLY MAXIMAL: |F' \ F| ≤ |F \ F'| for every matching [F']. *)
Definition strongly_maximal_matching (H : iHypergraph) (F : hE H -> Prop) : Prop :=
  hmatching F /\
  forall F' : hE H -> Prop, hmatching F' ->
    card_le (fun e => F' e /\ ~ F e) (fun e => F e /\ ~ F' e).

(** [X] is STRONGLY MINIMAL: |X \ X'| ≤ |X' \ X| for every cover [X']. *)
Definition strongly_minimal_cover (H : iHypergraph) (X : hV H -> Prop) : Prop :=
  hcover X /\
  forall X' : hV H -> Prop, hcover X' ->
    card_le (fun v => X v /\ ~ X' v) (fun v => X' v /\ ~ X v).

Definition strong_matchings_and_covers_statement : Prop :=
  forall (H : iHypergraph) (k : nat),
    (forall e : hE H, hedge_le k e) ->
    (exists F : hE H -> Prop, strongly_maximal_matching F) /\
    (exists X : hV H -> Prop, strongly_minimal_cover X).

(** ================================================================= *)
(** ** universal_highly_arc_transitive_digraphs  (Question, OPEN) *)

Record iDigraph := Build_iDigraph {
  dV : Type;
  darc : dV -> dV -> Prop;
  darc_irr : forall x, ~ darc x x }.

(** An automorphism: an adjacency-preserving bijection (the group ACTION, unfolded). *)
Definition dautomorphism (G : iDigraph) (f : dV G -> dV G) : Prop :=
  bijective f /\ forall x y, darc x y <-> darc (f x) (f y).

(** A directed path (all consecutive pairs are arcs). *)
Fixpoint darc_path (G : iDigraph) (p : seq (dV G)) : Prop :=
  match p with
  | [::] => True
  | x :: p' => match p' with
               | [::] => True
               | y :: _ => darc x y /\ darc_path p'
               end
  end.

(** HIGHLY ARC TRANSITIVE: the automorphism action is transitive on directed
    paths of every fixed length. *)
Definition highly_arc_transitive (G : iDigraph) : Prop :=
  forall p q : seq (dV G),
    darc_path p -> darc_path q -> size p = size q ->
    exists f : dV G -> dV G, dautomorphism f /\ map f p = q.

(** An ALTERNATING WALK [x :: p] with starting polarity [b] (each step's arc
    direction flips): [b] forward = [darc x y], backward = [darc y x]. *)
Fixpoint alt_walk_from (G : iDigraph) (b : bool) (x : dV G) (p : seq (dV G)) : Prop :=
  match p with
  | [::] => True
  | y :: p' => (if b then darc x y else darc y x) /\ alt_walk_from (~~ b) y p'
  end.

(** The alternating walk [x :: p] (polarity [b]) USES the arc [a → c]. *)
Fixpoint walk_uses (G : iDigraph) (b : bool) (x : dV G) (p : seq (dV G)) (a c : dV G) : Prop :=
  match p with
  | [::] => False
  | y :: p' =>
      ((b = true /\ x = a /\ y = c) \/ (b = false /\ y = a /\ x = c))
      \/ walk_uses (~~ b) y p' a c
  end.

(** UNIVERSAL: every pair of arcs lies on a common alternating walk. *)
Definition universal (G : iDigraph) : Prop :=
  forall a1 c1 a2 c2 : dV G, darc a1 c1 -> darc a2 c2 ->
    exists (b : bool) (x : dV G) (p : seq (dV G)),
      alt_walk_from b x p /\ walk_uses b x p a1 c1 /\ walk_uses b x p a2 c2.

(** LOCALLY FINITE: every vertex has finite out- and in-neighbourhoods. *)
Definition d_locally_finite (G : iDigraph) : Prop :=
  forall x : dV G,
    (exists ko (go : 'I_ko -> dV G), forall y, darc x y -> exists i, go i = y) /\
    (exists ki (gi : 'I_ki -> dV G), forall y, darc y x -> exists i, gi i = y).

(** Non-vacuity guards (preflight): a genuine arc exists; infinitely many
    vertices; and no sinks/sources (out- and in-degree ≥ 1) so the finite
    directed cycle and the edgeless digraph cannot satisfy the row vacuously. *)
Definition d_has_arc (G : iDigraph) : Prop := exists a b : dV G, darc a b.
Definition d_infinite (G : iDigraph) : Prop := exists f : nat -> dV G, injective f.
Definition d_no_sink_source (G : iDigraph) : Prop :=
  forall x : dV G, (exists y, darc x y) /\ (exists y, darc y x).

Definition universal_highly_arc_transitive_digraphs_statement : Prop :=
  exists G : iDigraph,
    [/\ d_locally_finite G, highly_arc_transitive G, universal G
      & [/\ d_has_arc G, d_infinite G & d_no_sink_source G] ].
