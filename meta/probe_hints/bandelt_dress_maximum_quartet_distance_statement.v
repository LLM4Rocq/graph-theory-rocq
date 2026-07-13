From GTBase Require Export base.
From GTMisc.conjectures Require Import X89.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma refuted : ~ bandelt_dress_maximum_quartet_distance_statement.
Proof.
rewrite /bandelt_dress_maximum_quartet_distance_statement.
move=> [f [P Q]].
(* two-thirds at q = 4 gives a threshold N *)
have [N HN] := Q 4 (isT : 3 <= 4).
pose n := N + 4.
have hnN : N <= n by rewrite /n leq_addr.
have hn4 : 4 <= n by rewrite /n leq_addl.
have [le1 _] := HN n hnN.       (* 3*4*f n <= (2*4+3) * 'C(n,4) *)
(* max-quartet-distance at n : get a witness tree T0 *)
have [[T0 [U0 _]] Hub] := P n.
(* build two trees sharing T0's graph/leaf but with constant shapes 0 and 1 *)
pose c0 : 'I_3 := @Ordinal 3 0 isT.
pose c1 : 'I_3 := @Ordinal 3 1 isT.
pose Ta := X89Tree (x89_tree_is_tree T0) (@x89_leaf_injective n T0)
             (x89_leaf_degree_one T0) (fun _ => c0).
pose Tb := X89Tree (x89_tree_is_tree T0) (@x89_leaf_injective n T0)
             (x89_leaf_degree_one T0) (fun _ => c1).
have Hd : x89_quartet_distance Ta Tb = 'C(n, 4).
  rewrite /x89_quartet_distance /=.
  have -> : [set Q0 : {set 'I_n} | (#|Q0| == 4) && (c0 != c1)]
          = [set Q0 : {set 'I_n} | #|Q0| == 4].
    apply/setP => Q0; rewrite !inE.
    by rewrite (_ : (c0 != c1) = true) ?andbT.
  by rewrite card_draws card_ord.
have Hle : 'C(n,4) <= f n by rewrite -Hd; apply: Hub.
(* now contradiction: 'C(n,4) <= f n but 12 * f n <= 11 * 'C(n,4) *)
have hb : 0 < 'C(n, 4) by rewrite bin_gt0.
move: le1.
have h12 : 12 * 'C(n,4) <= 12 * f n by rewrite leq_mul2l /=.
rewrite /=.
move=> le1'.
have : 12 * 'C(n,4) <= 11 * 'C(n,4).
  apply: leq_trans h12 _.
  by move: le1'; rewrite (mulnC 3 4).
rewrite leq_mul2r.
by rewrite (gtn_eqF hb) /= ltnn.
Qed.

Print Assumptions refuted.
