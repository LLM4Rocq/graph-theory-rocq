(** * Minor.conjectures.X127 -- v2 2-tree-width vs chromatic number row *)

From GTBase Require Export base.
From Minor.conjectures Require Import X27.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X127 vocabulary ***********************************************)

(** 2-tree-width (Dujmović–Joret–Morin–Norin–Wood; = the k=2 case of median
    tree-width, Felsner–Joret–Micek–Trotter–Wiechert arXiv:1703.07871).
    [x127_two_tree_width_le G k] holds iff G admits TWO tree-decompositions
    [(T1, bag1)] and [(T2, bag2)] (both index graphs arbitrary trees) whose bags
    are pairwise k-orthogonal: |B1_{t1} ∩ B2_{t2}| ≤ k for every t1 : T1, t2 : T2.
    "2" = the two decompositions; the parameter is the minimum such k, so
    "2-tree-width ≤ k" is exactly the existence of such a pair.  Every graph has
    2-tree-width ≤ |V(G)| via the single-bag decompositions, so it is finite
    (non-vacuous). *)
Definition x127_two_tree_width_le (G : sgraph) (k : nat) : Prop :=
  exists (T1 : sgraph) (bag1 : T1 -> {set G}) (T2 : sgraph) (bag2 : T2 -> {set G}),
    [/\ is_tree [set: T1], x27_tree_decomposition bag1,
        is_tree [set: T2], x27_tree_decomposition bag2 &
        forall (t1 : T1) (t2 : T2), #|bag1 t1 :&: bag2 t2| <= k].

(** ** X127 statements *****************************************************)

(** Dujmović–Joret–Morin–Norin–Wood question: is there a single function
    f : ℕ → ℕ such that every graph G of 2-tree-width at most k is f(k)-colourable?
    The ∃ f comes BEFORE the ∀ k, G (one universal function); chromatic number is
    the corpus [χ([set: G])].

    FAITHFUL-TO-REFUTED (like X14/X92/X73): this DJMNW question is now RESOLVED
    NEGATIVELY.  Felsner–Joret–Micek–Trotter–Wiechert (arXiv:1703.07871) show the
    Burling graphs G_k have χ(G_k) ≥ k (Thm 1) yet admit a tree-decomposition and
    a path-decomposition — hence two tree-decompositions — with all pairwise bag
    intersections ≤ 2 (Thm 2), i.e. 2-tree-width ≤ 2 with unbounded χ; so no such
    f exists and the statement below is FALSE.  The encoding is nonetheless the
    faithful reading of the row's (open-as-recorded) question — the leg tracks
    faithful formalization, not truth.  Note: this is DISTINCT from FJMTW's
    separate still-open Conjecture 3 (which restricts to a *spaghetti*
    tree-decomposition orthogonal to a path-decomposition). *)
Definition dujmovic_joret_morin_norin_wood_two_tree_width_chi_statement : Prop :=
  exists f : nat -> nat,
    forall (k : nat) (G : sgraph),
      x127_two_tree_width_le G k ->
      χ([set: G]) <= f k.
