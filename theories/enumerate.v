Require Import Recdef.
From mathcomp Require Import all_ssreflect all_algebra finmap.
Require Import extra_misc inner_product extra_matrix xorder vector_order row_submx vector_order.
Require Import hpolyhedron polyhedron barycenter poly_base.
Require Import enumeration graph MapFold.
From Bignums Require Import BigQ.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory.
Import GRing.Theory Num.Theory.

Open Scope ring_scope.

Section Perturbation.

Context (R : realFieldType) (n m: nat).

Definition sat_ineq (l : 'rV[R]_n * 'rV[R]_(S m)) x : bool :=
  (l.1 *m x) <=lex (l.2).
Definition sat_eq (l : 'rV[R]_n * 'rV[R]_(S m)) x : bool :=
  (l.1 *m x) == (l.2).
End Perturbation.

Module PolyPrerequisite <: Prerequisite.
Parameters (n m : nat).
Definition U := 'M[rat]_(n, m.+1).
Definition L := ('rV[rat]_n * 'rV[rat]_(m.+1))%type.
Definition sat_ineq := @sat_ineq [realFieldType of rat] n m.
Definition sat_eq := @sat_eq [realFieldType of rat] n m.
End PolyPrerequisite.

Module PolyAlgorithm := Algorithm PolyPrerequisite.

Section Refinement.

Context (f : rat -> bigQ).
Hypothesis f_inj : forall x y, (f x == f y)%bigQ -> x = y.

Definition f_rV (n : nat) (x : 'rV[rat]_n) : seq bigQ :=
  [seq (f (x 0 j)) | j <- ord_enum n].

Definition f_cV (n : nat) (x : 'cV[rat]_n) : seq bigQ :=
  [seq (f (x j 0)) | j <- ord_enum n].

Definition f_L (n m: nat) (x : 'rV[rat]_n * 'rV[rat]_(S m)) :
  (seq bigQ * seq bigQ) :=
  (f_rV x.1, f_rV x.2).

Definition f_U (n m: nat) (x : 'M[rat]_(n, m.+1)) : seq (seq bigQ) :=
  [seq (f_cV (col j x)) | j <- ord_enum m.+1].
(*return the transpose to make further computations easier*)

Fixpoint in_seqQ x (s : seq bigQ) :=
  match s with
    |[::] => false
    |h::t => if BigQ.eqb h x then true else in_seqQ x t
  end.


Fixpoint lex_order (x y : seq bigQ) :=
  match x, y with
  |[::], [::] => true
  |hx::tx, hy::ty => match (hx ?= hy)%bigQ with
    |Lt => true
    |Gt => false
    |Eq => lex_order tx ty
    end
  |_, _ => false
end.

Definition dot (x y : seq bigQ) : bigQ :=
  let aux := (fun res p => BigQ.add_norm res (BigQ.mul_norm p.1 p.2)) in
  foldl aux 0%bigQ (zip x y).

Definition product (l : seq bigQ) (u : seq (seq bigQ)) :=
  (map (fun e => dot l e) u).

Definition ref_sat_ineq (l : seq bigQ * seq bigQ) (u : seq (seq bigQ)) :=
  lex_order (product l.1 u) l.2.

Definition ref_sat_eq (l : seq bigQ * seq bigQ) (u : seq (seq bigQ)) :=
  all2 BigQ.eqb (product l.1 u) l.2.

Section Proofs.

Lemma bigQ_eqP x y: reflect (BigQ.eq x y) (BigQ.eqb x y).
Proof.
rewrite/BigQ.eqb; apply/(iffP idP);
  [exact: BigQ.eqb_correct | exact: BigQ.eqb_complete].
Qed.

Lemma all_bigQ (s : seq bigQ) (P : pred bigQ) :
  all P s -> (forall x y, (x == y)%bigQ -> P x = P y) ->
  (forall x, in_seqQ x s -> P x).
Proof.
elim: s => // a l HI /= /andP [P_a all_l] P_prop x.
case/boolP: (BigQ.eqb a x).
- by move/bigQ_eqP/P_prop => <-.
- move=> _; exact: HI.
Qed.

Lemma all2_bigQ (r s : seq bigQ) (R : rel bigQ) :
  all2 R r s ->
  (forall x y x' y', (x == x')%bigQ -> (y == y')%bigQ -> R x y = R x' y') ->
  (forall x y, in_seqQ x r -> in_seqQ y s -> R x y).
Proof.
Admitted.

Lemma in_frVP (n : nat) (x : 'rV[rat]_n) v :
  reflect (exists i, f (x 0 i) = v) (in_seqQ v (f_rV x)).
Proof.
apply/(iffP idP); rewrite/f_rV.
- elim: (ord_enum n) => // a l HI; rewrite map_cons /=.
Admitted.

Lemma in_fcVP (n : nat) (x : 'cV[rat]_n) v :
  reflect (exists i, f (x i 0) = v) (in_seqQ v (f_cV x)).
Proof.
Admitted.


Lemma frV_inj (n : nat) (x y : 'rV[rat]_n) :
  all2 BigQ.eqb (f_rV x) (f_rV y) -> x = y.
Proof.
Admitted.

Lemma fcV_inj (n : nat) (x y : 'cV[rat]_n) :
  all2 BigQ.eqb (f_cV x) (f_cV y) -> x = y.
Proof.
Admitted.


Lemma ref_dot (n : nat) (x : 'rV_n) (y : 'cV_n) :
  dot (f_rV x) (f_cV y) = f ((x *m y) 0 0).
Admitted.

Lemma ref_product (n m : nat) (x : 'rV_n) (u : 'M_(n, m.+1)) :
  product (f_rV x) (f_U u) = (f_rV (x *m u)).
Admitted.

Lemma ref_lex (n : nat) (x y : 'rV_n) :
  lex_order (f_rV x) (f_rV y) = x <=lex y.
Admitted.

Lemma sat_ineq_foo (n m : nat) (l : 'rV_n * 'rV_m.+1) (u: 'M_(n,m.+1)) :
  sat_ineq l u = ref_sat_ineq (f_L l) (f_U u).
Proof.
rewrite/sat_ineq/ref_sat_ineq/f_L /=.
by rewrite ref_product ref_lex.
Qed.

Lemma sat_eq_foo (n m : nat) (l : 'rV_n * 'rV_m.+1) (u: 'M_(n,m.+1)) :
  sat_eq l u = ref_sat_eq (f_L l) (f_U u).
Proof.
Admitted.

End Proofs.

End Refinement.

Module RefPrerequisite <: Prerequisite.
Definition U := seq (seq bigQ).
Definition L := (seq bigQ * seq bigQ)%type.
Definition sat_ineq := ref_sat_ineq.
Definition sat_eq := ref_sat_eq.
End RefPrerequisite.

Module RefAlgorithm := Algorithm RefPrerequisite.

Module PA := PolyAlgorithm.
Module RA := RefAlgorithm.
Module PG := PolyAlgorithm.AlgoGraph.
Module RG := RefAlgorithm.AlgoGraph.

Section GraphStructure.

Variable n : nat.
Variable G1 : PolyAlgorithm.AlgoGraph.t.
Variable G2 : RefAlgorithm.AlgoGraph.t.

Definition eqv_graph :=
  (PG.mem_vertex^~ G1 =1 RG.mem_vertex^~ G2) /\
  (forall v1 v2, PG.mem_edge v1 v2 G1 = RG.mem_edge v1 v2 G2).


Lemma eqv_struct_consistent : eqv_graph ->
  PolyAlgorithm.struct_consistent n G1 = RefAlgorithm.struct_consistent n G2.
Proof.
move=> eqv_G12; rewrite /PA.struct_consistent /RA.struct_consistent.
rewrite (PG.vertex_all_eq _ (PG.assoc_listP G1)).
rewrite (RG.vertex_all_eq _ (RG.assoc_listP G2)).
rewrite /PA.neighbour_condition /RA.neighbour_condition.


move=> G1_eqv_G2; rewrite /PA.struct_consistent /PG.vertex_all.
rewrite (@PG.vertex_foldE _ _ G1 _ (unzip1 (PG.adjacency_list G1))); first last => //.
- by case => //= ??; rewrite andbC.
- admit.
- have ->:
  (fun x =>  andb^~ (PA.neighbour_condition n G1 x)) =
  (fun x => andb^~ (RA.neighbour_condition n G2 x)) by admit.
  rewrite -(@RG.vertex_foldE _ _ G2) => //.
- admit.
- admit.
- admit.
Admitted.

End GraphStructure.





