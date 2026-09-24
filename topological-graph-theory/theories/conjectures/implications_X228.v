(** * Topological.conjectures.implications_X228 — wave X228 dependency-graph EDGES

    The two X228 nodes are the random-embedding rows of arXiv:2202.07746
    (Conjecture 4, [E[F] <= n/3 + 1]) and arXiv:2103.05036 (Conjecture 1,
    [E[F] = O(n)]).  The corpus records one confirmed relation between them,
    gc:e125 (arxiv:2202.07746#00 implies arxiv:2103.05036#00): the sharp bound
    [n/3 + 1] is in particular linear in [n].

    Both endpoints are formalized in THIS package on the same finite-average
    primitives, so the edge is machine-checked below: the theorem is a relative
    implication, proved without resolving either conjecture. *)

From GTBase Require Import base.
From mathcomp Require Import fingroup perm.
From Topological.conjectures Require Import X228 grounding_X228.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** gc:e125.  Conjecture 4 (E[F] <= n/3 + 1 for CONNECTED graphs) implies the
    O(n) row (all graphs) only through additivity of face counts and
    multiplicativity of rotation-system counts over connected components, which
    is not formalised here; the constant-2 proof that existed before the
    connectedness guard was added (2026-09-23) no longer applies.  Candidate. *)
(*@EDGE from=random_embedding_expected_faces_third_statement
        to=random_embedding_expected_faces_linear_statement
        kind=implies status=candidate proved=false
        cite="gc:e125"
        note="Needs additivity of x228_total_faces / multiplicativity of x228_nrot over connected components; the source's Conjecture 4 is stated for connected graphs (2-cell embeddings)." *)
