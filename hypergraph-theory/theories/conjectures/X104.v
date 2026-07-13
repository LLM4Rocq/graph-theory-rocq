(** * Hypergraph.conjectures.X104 -- v2 Brown-Erdos-Sos row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X104 vocabulary ***********************************************)

Definition x104_uniform (T : finType) (E : {set {set T}}) (r : nat) : Prop :=
  forall e : {set T}, e \in E -> #|e| = r.

Definition x104_span (T : finType) (F : {set {set T}}) : {set T} :=
  [set v : T | [exists e : {set T}, (e \in F) && (v \in e)]].

Definition x104_brown_erdos_sos_free
    (T : finType) (E : {set {set T}}) (e : nat) : Prop :=
  forall F : {set {set T}},
    F \subset E ->
    #|F| = e ->
    e + 3 < #|x104_span F|.

(** ** X104 statements *****************************************************)

(** Studies slice: Brown-Erdos-Sos conjecture for 3-uniform hypergraphs:
    for each fixed e >= 3, the extremal number f(n,e+3,e) is o(n^2). *)
Definition brown_erdos_sos_three_uniform_statement : Prop :=
  forall e eps_num eps_den : nat,
    3 <= e ->
    0 < eps_num ->
    0 < eps_den ->
    exists N : nat,
      forall (T : finType) (E : {set {set T}}),
        N <= #|T| ->
        x104_uniform E 3 ->
        x104_brown_erdos_sos_free E e ->
        eps_den * #|E| <= eps_num * (#|T| ^ 2).
