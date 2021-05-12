Require Import Recdef.
From mathcomp Require Import all_ssreflect all_algebra finmap.
Require Import extra_misc inner_product extra_matrix xorder vector_order row_submx vector_order.
Require Import hpolyhedron polyhedron barycenter poly_base.
Require Import enumeration graph MapFold enumEquiv.
Require Import high_graph.
From Bignums Require Import BigQ.
Require Import Setoid.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory.
Import GRing.Theory Num.Theory.

Open Scope ring_scope.

Section Perturbation.

Context {n : nat} (base : base_t[rat,n]).

Definition create_perturbation {m : nat} (b : rat) (k : 'I_m) : 'rV_m.+1 :=
  @row_mx _ _ 1 m (const_mx b) (row k (pid_mx m)).


Definition perturbation :=
  map
  (fun x: lrel * 'I_(#|`base|) => (x.1.1^T , create_perturbation x.1.2 x.2))
  (zip (enum_fset base) (ord_enum #|`base|)).

(*TODO A-t-on x \in P : {poly base} => x \in perturbation ? Même chose avec des sommets ?*)

End Perturbation.

Section LexiBasis.

Context {n m: nat} (base_p : seq ('rV[rat]_n * 'rV[rat]_m.+1)).

Definition sat_prebasis (x : 'M[rat]_(n,m.+1)) :=
  all (fun l => sat_ineq l x) base_p.

Definition eq_prebasis (mas : bitseq) (x : 'M[rat]_(n, m.+1)) :=
  all (fun l => sat_eq l x) (mask mas base_p).

Definition lexi_preaxiom (b : (bitseq * 'M[rat]_(n,m.+1))%type) :=
  [&& sat_prebasis b.2, card_bitseq b.1 == n & eq_prebasis b.1 b.2].

Record lexi_prebasis := Lexi {
  prebase :> (bitseq * 'M[rat]_(n,m.+1))%type;
  preaxiom : lexi_preaxiom prebase
}.

Coercion lexi_mask (L : lexi_prebasis) : bitseq := L.1.
Coercion lexi_point (L : lexi_prebasis) : 'M[rat]_(n, m.+1) := L.2.
  
Canonical prelexi_subType := [subType for prebase].
Definition prelexi_eqMixin := [eqMixin of lexi_prebasis by <:].
Canonical prelexi_eqType := EqType _ prelexi_eqMixin.
Definition prelexi_choiceMixin := [choiceMixin of lexi_prebasis by <:].
Canonical prelexi_choiceType := ChoiceType _ prelexi_choiceMixin.

Lemma lexi_preaxiomP (L : lexi_prebasis) :
  lexi_preaxiom L.
Proof. exact: preaxiom. Qed.

Lemma lexi_sat_prebasis (L : lexi_prebasis) : sat_prebasis L.
Proof. by case/and3P: (lexi_preaxiomP L). Qed.

Lemma lexi_card (L : lexi_prebasis) :
  card_bitseq L == n.
Proof. by case/and3P: (lexi_preaxiomP L). Qed.

Lemma lexi_eq_prebasis (L: lexi_prebasis) : eq_prebasis L L.
Proof. by case/and3P: (lexi_preaxiomP L). Qed.


(* ------------------------------------------------------------------- *)

Definition is_basis (L : lexi_prebasis) : bool :=
  \dim <<(mask L (unzip1 base_p))>>%VS == n.
  

Record lexi_basis := LexiB
  {
    lbase :> lexi_prebasis;
    lbase_is_basis : is_basis lbase
  }.

Canonical lexi_subType := [subType for lbase].
Definition lexi_eqMixin := [eqMixin of lexi_basis by <:].
Canonical lexi_eqType := EqType _ lexi_eqMixin.
Definition lexi_choiceMixin := [choiceMixin of lexi_basis by <:].
Canonical lexi_choiceType := ChoiceType _ lexi_choiceMixin.

Lemma lexi_basisP (L : lexi_basis) : is_basis L.
Proof. by case: L. Qed.

Definition matrix_of_seqrV {k : nat} {R : realFieldType}
  (s : seq 'rV[R]_k) :=
  \matrix_(i < size s) nth (\row_(j < k) 0) s i.





(* Lemma eq_prebasisE (mas : bitseq) (x : 'M[rat]_(n, m.+1)):
  (eq_prebasis mas x) =
  (matrix_of_seqrV (mask mas (unzip1 base_p)) *m x == 
  matrix_of_seqrV (mask mas (unzip2 base_p))). *)

Lemma lexi_pointP (L : lexi_basis) x:
  eq_prebasis L x -> x = L.
Proof.
rewrite /eq_prebasis /sat_eq.



End LexiBasis.






