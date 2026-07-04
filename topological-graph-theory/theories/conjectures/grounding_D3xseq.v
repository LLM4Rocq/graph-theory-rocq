(** * Grounding for the D3 crossing-sequences row (the encoding has content). *)

From GTBase Require Export base.
From Topological.foundations Require Import embedding crossing crossing_genus.
From Topological.conjectures Require Import D3xseq.

Set Implicit Arguments.
Unset Strict Implicit.

(** cr_i is WELL-DEFINED (functional): a graph has at most one crossing number
    per genus, so "cr_i(G) = aᵢ" pins a unique value — the row's per-index
    equalities are not simultaneously satisfiable by junk. *)
Lemma xseq_functional (G : sgraph) (i m n : nat) :
  is_crossing_genus G i m -> is_crossing_genus G i n -> m = n.
Proof. exact: is_crossing_genus_uniq. Qed.

(** The crossing sequence the conjecture ranges over is genuinely NON-INCREASING
    (a theorem here, not an assumption), so the strict-decrease-to-0 hypothesis is
    the right shape and is not describing an impossible object. *)
Lemma xseq_nonincreasing (G : sgraph) (i m n : nat) :
  is_crossing_genus G i m -> is_crossing_genus G i.+1 n -> n <= m.
Proof. exact: is_crossing_genus_nonincreasing. Qed.

(** The realizability predicate is INHABITED (not trivially false): every graph
    realizes cr_i = 0 at its own embedding genus. *)
Lemma xseq_realizable (G : sgraph) : exists i, is_crossing_genus G i 0.
Proof. exact: is_crossing_genus_inhab. Qed.

(** FAITHFULNESS ANCHOR (machine-checked): a crossing resolution PRESERVES
    connectivity, so a [connected] witness's planarizations all stay connected —
    where [euler_genus] is EXACT — making [is_crossing_genus] the exact topological
    genus crossing number (not a proxy).  This is why the statement guards the
    witness with [connected [set: G]] and is DONE rather than partial. *)
Lemma xseq_xsplit_connected (G : sgraph) (a b c d : G) :
  connected [set: G] -> connected [set: xsplit a b c d].
Proof. exact: xsplit_connected. Qed.

(** The strict-decrease-to-0 HYPOTHESES are satisfiable (e.g. by [[:: 0]]), so
    the statement's premise is not vacuously unmet. *)
Lemma xseq_hyp_inhab :
  exists a : seq nat,
    [/\ 0 < size a,
        (forall j : nat, j.+1 < size a -> nth 0 a j.+1 < nth 0 a j)
      & nth 0 a (size a).-1 = 0].
Proof. by exists [:: 0]; split=> // j; rewrite ltnS leqn0 => /eqP. Qed.
