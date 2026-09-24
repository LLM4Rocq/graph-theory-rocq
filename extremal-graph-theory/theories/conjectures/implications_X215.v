(** * Extremal.conjectures.implications_X215 -- corpus relation edges unlocked by wave X215.

    The X215 rows own exactly one confirmed [implies] relation of
    meta/corpus_relations.json with both endpoints formalised, namely e239
    (bm:bm-033 => bm:bm-039, Erdos-Sos implies the Burr-Erdos tree Ramsey bound).
    It is discharged below as a Qed-closed relative theorem, so the edge is
    recorded with status=verified.

    The remaining X215 rows (bm-034 even-cycle Turan, bm-037 and bm-038, both
    BLOCKED) are endpoints of no confirmed corpus relation. *)

From GTBase Require Import base.
From Stdlib Require Import Lia.
From Extremal.foundations Require Import edge_colourings.
From Extremal.conjectures Require Import X215.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The textbook reduction: in a 2-colouring of K_{2k} one colour class carries
    at least half of the 'C(2k,2) = k(2k-1) edges, which already exceeds the
    Erdos-Sos threshold n(k-1)/2 = 2k(k-1)/2 for n = 2k. *)
Theorem erdos_sos_implies_burr_erdos_tree_ramsey :
  erdos_sos_tree_embedding_statement -> burr_erdos_tree_ramsey_statement.
Proof.
move=> ES T k N tT eT vT k0 -> col.
have bin2_double : forall m : nat, 'C(2 * m, 2) = m * (2 * m).-1.
  by move=> m; rewrite bin2 mul2n -doubleMl doubleK.
have arith : forall m : nat, 0 < m -> 2 * m * m < m * (2 * m).-1 + 2 * m.
  case=> // j _.
  have -> : (2 * j.+1).-1 = (2 * j).+1 by rewrite mulnS.
  by apply/ltP; rewrite -!plusE -!multE; lia.
have [c Hc] := majority_colour col.
rewrite card_edge_Kn bin2_double in Hc.
have cardV : #|colour_class col (pred1 c)| = 2 * k by rewrite card_ord.
have HG : #|colour_class col (pred1 c)| * k
        < 2 * #|E(colour_class col (pred1 c))|
          + #|colour_class col (pred1 c)|.
  rewrite cardV.
  apply: leq_trans (_ : k * (2 * k).-1 + 2 * k <= _); last by rewrite leq_add2r.
  exact: (arith k k0).
by exists c; apply/mono_copyP; exact: (ES _ _ _ tT eT vT HG).
Qed.

(*@EDGE from=erdos_sos_tree_embedding_statement to=burr_erdos_tree_ramsey_statement kind=implies status=verified proof=erdos_sos_implies_burr_erdos_tree_ramsey cite="gc:e239" *)

Print Assumptions erdos_sos_implies_burr_erdos_tree_ramsey.
