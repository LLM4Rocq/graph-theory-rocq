(** * Packing.conjectures.X111 -- v2 ball-hypergraph transversal/packing row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X111 vocabulary ************************************************)

(** The closed r-ball around [x] (all vertices at graph distance <= r).
    Replicated locally from the X39 idiom to avoid a cross-repo import;
    [x111_ball 0 x = [set x]] and each step adds the neighbourhoods of the
    current ball.  Since [x \in x111_ball r x] for every [r], every ball is
    NONEMPTY. *)
Fixpoint x111_ball (G : sgraph) (r : nat) (x : G) : {set G} :=
  if r is r'.+1 then x111_ball r' x :|: \bigcup_(z in x111_ball r' x) N(z)
  else [set x].

(** The r-ball hypergraph of [G] with centre set [U] has hyperedges
    { B(u,r) : u \in U }.  [T] is a TRANSVERSAL of it when [T] meets every
    such ball. *)
Definition x111_is_transversal (G : sgraph) (r : nat) (U T : {set G}) : bool :=
  [forall u, (u \in U) ==> (T :&: x111_ball r u != set0)].

(** [S] is a PACKING when [S] selects a subfamily of the hyperedges (so
    [S \subset U]) whose balls are pairwise DISJOINT.  As balls are nonempty,
    two distinct centres with the same ball are never both packed, matching the
    hypergraph reading. *)
Definition x111_is_packing (G : sgraph) (r : nat) (U S : {set G}) : bool :=
  (S \subset U) &&
  [forall u, [forall v,
     (u \in S) ==> (v \in S) ==> (u != v) ==>
     [disjoint x111_ball r u & x111_ball r v]]].

(** τ(H): the transversal (covering) number — the LEAST size of a transversal.
    The full vertex set [[set: G]] is always a transversal (each [u \in B(u,r)]),
    so it is a valid arg-min default and the result is the genuine minimum. *)
Definition x111_tau (G : sgraph) (r : nat) (U : {set G}) : nat :=
  #|[arg min_(T < [set: G] | x111_is_transversal r U T) #|T|]|.

(** ν(H): the packing (matching) number — the GREATEST size of a packing.
    The empty set is always a packing, so the maximum is over a nonempty
    family and [x111_nu] is total. *)
Definition x111_nu (G : sgraph) (r : nat) (U : {set G}) : nat :=
  \max_(S : {set G} | x111_is_packing r U S) #|S|.

(** ** X111 statements ******************************************************)

(** Chepoi–Estellon–Vaxès conjecture.  There is a UNIVERSAL constant [c]
    (∃ BEFORE all the ∀'s — one constant for every instance) such that for
    every radius [r], every PLANAR graph [G] ([wagner_planar]) and every choice
    of ball centres [U ⊆ V(G)], the transversal number of the r-ball hypergraph
    is at most [c] times its packing number:  τ(H) ≤ c · ν(H).  This is a
    bounded covering-vs-packing (fractional-Helly-flavoured) ratio for ball
    hypergraphs of planar graphs; τ and ν range over the SAME centre set [U].
    Empty [U] gives τ = ν = 0 (the bound still holds), and any nonempty [U]
    forces ν ≥ 1, so the statement is not vacuous. *)
Definition chepoi_estellon_vaxes_ball_hypergraph_transversal_statement : Prop :=
  exists c : nat,
    forall (r : nat) (G : sgraph),
      wagner_planar G ->
      forall U : {set G},
        x111_tau r U <= c * x111_nu r U.
