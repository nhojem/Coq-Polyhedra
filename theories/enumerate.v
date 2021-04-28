Require Import Recdef.
From mathcomp Require Import all_ssreflect all_algebra finmap.
Require Import extra_misc inner_product extra_matrix xorder vector_order row_submx vector_order.
Require Import hpolyhedron polyhedron barycenter poly_base.
Require Import enumeration graph MapFold.
From Bignums Require Import BigQ.
Require Import Setoid.

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

Module PA := PolyAlgorithm.
Module BQA := BigQAlgorithm.
Module PG := PolyAlgorithm.AlgoGraph.
Module BQG := BigQAlgorithm.AlgoGraph.
Module PP := PolyPrerequisite.
Module BQP := BigQPrerequisite.

Section GraphStructure.

Variable n : nat.
Variable G1 : PG.t.
Variable G2 : BQG.t.

Definition eqv_graph :=
  (PG.mem_vertex^~ G1 =1 BQG.mem_vertex^~ G2) /\
  (forall v1 v2, PG.mem_edge v1 v2 G1 = BQG.mem_edge v1 v2 G2).

Lemma perm_eqv_graph: eqv_graph ->
  perm_eq (PG.vertex_list G1) (BQG.vertex_list G2).
Proof.
rewrite /PG.adj_list /BQG.adj_list.
case=> ? _; apply: uniq_perm; rewrite ?PG.MF.uniq_keys ?BQG.MF.uniq_keys //.
by move=> v; rewrite PG.vtx_mem_list BQG.vtx_mem_list.
Qed.


Lemma eqv_struct_consistent : eqv_graph ->
  PA.struct_consistent n G1 = BQA.struct_consistent n G2.
Proof.
move=> [eqvtx eqedg]; rewrite /PA.struct_consistent /BQA.struct_consistent.
rewrite (PG.vertex_all_eq _ (PG.adj_listP G1)).
rewrite (BQG.vertex_all_eq _ (BQG.adj_listP G2)) -!all_map.
rewrite (@eq_all _ (PA.neighbour_condition n G1) (BQA.neighbour_condition n G2)).
  exact/perm_all/perm_eqv_graph.
move=> I; rewrite /PA.neighbour_condition /BQA.neighbour_condition.
case E: (PG.mem_vertex I G1).
- rewrite (@PG.neighbour_all_eq _ _ (PG.neighbour_list G1 I)) //.
  rewrite eqvtx in E.
  rewrite (@BQG.neighbour_all_eq _ _ (BQG.neighbour_list G2 I)) //.
  have perm_nei: perm_eq (PG.neighbour_list G1 I) (BQG.neighbour_list G2 I).
  + apply/uniq_perm; rewrite ?PG.uniq_neighbour_list ?BQG.uniq_neighbour_list //.
    by move=> x; rewrite -PG.edge_mem_list -BQG.edge_mem_list eqedg.
  congr (_ && _); first exact/perm_all.
  + rewrite (PG.nb_neighbours_list) ?(BQG.nb_neighbours_list) ?eqvtx //.
    by rewrite (perm_size perm_nei).
  + rewrite PG.neighbour_allF ?BQG.neighbour_allF -?eqvtx ?E //=.
    by rewrite PG.nb_neighboursF ?BQG.nb_neighboursF -?eqvtx ?E.
Qed.

End GraphStructure.

Section Refinement.

Context (f : rat -> bigQ).
Hypothesis f_inj : forall x y, (f x == f y)%bigQ -> x = y.

Definition f_rV (n : nat) (x : 'rV[rat]_n) : seq bigQ :=
  [seq (f (x 0 j)) | j <- ord_enum n].

Definition f_cV (n : nat) (x : 'cV[rat]_n) : seq bigQ :=
  [seq (f (x j 0)) | j <- ord_enum n].

Definition f_L (x : PP.L) : BQP.L :=
  (f_rV x.1, f_rV x.2).

Definition f_U (x : PP.U) : BQP.U :=
  [seq (f_cV (col j x)) | j <- ord_enum (PP.m).+1].
(*return the transpose to make further computations easier*)

Section Proofs.

Add Relation bigQ BigQ.eq
  reflexivity proved by (@Equivalence_Reflexive _ _ BigQ.eq_equiv)
  symmetry proved by (@Equivalence_Symmetric _ _ BigQ.eq_equiv)
  transitivity proved by (@Equivalence_Transitive _ _ BigQ.eq_equiv)
as bigQ_eq_rel.

Add Parametric Morphism : f with signature eq ==> BigQ.eq as f_morph.
Proof. move=> ?; exact: (@Equivalence_Reflexive _ _ BigQ.eq_equiv). Qed.


Lemma bigQ_eqP x y: reflect (BigQ.eq x y) (BigQ.eqb x y).
Proof.
rewrite/BigQ.eqb; apply/(iffP idP);
  [exact: BigQ.eqb_correct | exact: BigQ.eqb_complete].
Qed.


Lemma sat_ineq_foo (l : PP.L) (u: PP.U) :
  PP.sat_ineq l u = BQP.sat_ineq (f_L l) (f_U u).
Proof.
Admitted.

Lemma sat_eq_foo (l : PP.L) (u: PP.U) :
  PP.sat_eq l u = BQP.sat_eq (f_L l) (f_U u).
Proof.
Admitted.

Section GraphData.

Variable G1 : PG.t.
Variable G2 : BQG.t.
Context (Po : seq PP.L).

Definition eqv_data := forall v,
  omap f_U (PG.label v G1) = BQG.label v G2.

Lemma eqv_vertex_consistent: (eqv_graph G1 G2) -> eqv_data ->
  PA.vertex_consistent Po G1 =
  BQA.vertex_consistent [seq f_L x | x <- Po] G2.
Proof.
rewrite /PA.vertex_consistent /BQA.vertex_consistent.
case=> eqvtx eqedge eqv_d.
rewrite /PA.mask_eq /PA.sat_Po /BQA.mask_eq /BQA.sat_Po.
have fun1: forall x,
  PP.sat_eq^~ x =1 (fun y => BQP.sat_eq (f_L y) (f_U x)).
- by move=> x y; rewrite sat_eq_foo.
have fun2: forall x, PP.sat_ineq^~ x =1 (fun y=> BQP.sat_ineq (f_L y) (f_U x)).
- by move=> x y; rewrite sat_ineq_foo.
apply/(sameP idP)/(iffP idP).
- move/BQG.vertex_allP => BQGall; apply/PG.vertex_allP => v [l n] PG_find /=.
  move: (PG.find_mem PG_find); rewrite eqvtx; case/BQG.vtx_memE.
  case=> l' n' BQG_find; move: (eqv_d v).
  rewrite /PG.label /BQG.label /PG.find_vertex /BQG.find_vertex in PG_find BQG_find *.
  rewrite PG_find BQG_find /= => /Some_inj lel'.
  rewrite (eq_all (fun1 l)) (eq_all (fun2 l)) lel'.
  move: (BQGall _ _ BQG_find); rewrite -map_mask !all_map.
  case/andP => all1 all2; apply/andP; split.
  + by rewrite (@eq_all _ _ (preim [eta f_L] (BigQPrerequisite.sat_eq^~ (l', n').1))).
  + by rewrite (@eq_all _ _ (preim [eta f_L] (BigQPrerequisite.sat_ineq^~ (l', n').1))).
- move/PG.vertex_allP => PGall; apply/BQG.vertex_allP => v [l n] BQG_find.
  move: (BQG.find_mem BQG_find); rewrite -eqvtx; case/PG.vtx_memE.
  case=> l' n' PG_find; move: (eqv_d v).
  rewrite /PG.label /BQG.label /PG.find_vertex /BQG.find_vertex in BQG_find PG_find *.
  rewrite BQG_find PG_find /= => /Some_inj lel'.
  case/andP: (PGall _ _ PG_find); rewrite -map_mask !all_map.
  move=> all1 all2; apply/andP; split.
  + rewrite (@eq_all _ _ (PolyPrerequisite.sat_eq^~ (l', n').1)) //.
    by move=> ?; rewrite fun1 lel'.
  + rewrite (@eq_all _ _ (PolyPrerequisite.sat_ineq^~ (l', n').1)) //.
    by move=> ?; rewrite fun2 lel'.
Qed.

  
  


End GraphData.
End Proofs.

End Refinement.




  







