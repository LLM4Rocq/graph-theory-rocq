(** * Extremal.conjectures.X115 -- v2 Chvatal-Tuza odd induced cycles row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X115 vocabulary ***********************************************)

(** Internal adjacency of a vertex set: an edge of [G] both of whose ends lie
    in [S].  Reachability under this relation is connectedness of the induced
    subgraph [G[S]] using only [S]-internal edges. *)
Definition x115_scycle_rel (G : sgraph) (S : {set G}) : rel G :=
  fun x y => [&& x \in S, y \in S & x -- y].

Definition x115_connected (G : sgraph) (S : {set G}) : bool :=
  [forall x in S, [forall y in S, connect (x115_scycle_rel S) x y]].

(** Every vertex of [S] has exactly two neighbours inside [S], i.e. the induced
    subgraph [G[S]] is 2-regular. *)
Definition x115_two_regular (G : sgraph) (S : {set G}) : bool :=
  [forall x in S, #|N(x) :&: S| == 2].

(** [G[S]] is an induced cycle iff [S] has at least 3 vertices, is 2-regular,
    and is connected; it is *odd* when [#|S|] is odd.  A 2-regular connected
    graph on >= 3 vertices is exactly a cycle. *)
Definition x115_odd_induced_cycle (G : sgraph) (S : {set G}) : bool :=
  [&& 3 <= #|S|, odd #|S|, x115_two_regular S & x115_connected S].

Definition x115_count (G : sgraph) : nat :=
  #|[set S : {set G} | x115_odd_induced_cycle S]|.

(** ** X115 statements *****************************************************)

(** Chvatal--Tuza (1988): the maximum possible number of odd induced cycles in
    a graph on [n] vertices is [3 ^ (n / 3)].  Resolved by Morrison--Scott
    (arXiv:1603.02960, Theorem 1.6): the maximum [m_o(n)] equals [3^{n/3}] up
    to an [O(n)] additive term when [n = 3 (mod 6)] and up to a constant factor
    otherwise, and only for all [n >= n0].  Since [3^{n/3}] is not an integer,
    the bound [count <= 3^{n/3}] is cubed to [count^3 <= 3^n] (equivalent over
    the naturals).  We encode the resolved statement -- "the maximum is
    [Theta(3^{n/3})]" -- as a two-sided constant-factor bound with a threshold
    [N]: an upper constant [Cu] bounding every graph, and a lower constant [Cl]
    witnessed by an extremal graph at each [n >= N]. *)
Definition chvatal_tuza_max_odd_induced_cycles_statement : Prop :=
  exists Cu Cl N : nat,
    [/\ 0 < Cu, 0 < Cl,
        forall (n : nat) (G : sgraph),
          N <= n -> #|G| = n -> (x115_count G) ^ 3 <= Cu * 3 ^ n
      & forall n : nat,
          N <= n ->
          exists G : sgraph, #|G| = n /\ 3 ^ n <= Cl * (x115_count G) ^ 3].
