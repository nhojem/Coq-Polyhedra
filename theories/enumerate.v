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

Context (r : rat -> bigQ -> bool).

Hypothesis r_inj : forall x y a b, x = y -> (a == b)%bigQ -> r x a -> r y b.
Hypothesis r_0 : r 0 0%bigQ.
Hypothesis r_mul : forall x y a b, r (x * y) (BigQ.mul_norm a b).
Hypothesis r_add : forall x y a b, r (x + y) (BigQ.add_norm a b).

Definition r_rV (n : nat) (v : 'rV[rat]_n) (s : seq bigQ) :=
  (size s == n) && (all (fun k => r (v 0 k) (nth 0%bigQ s k)) (enum 'I_n)).

Definition r_cV (n : nat) (v : 'cV[rat]_n) (s : seq bigQ) :=
  (size s == n) && (all (fun k => r (v k 0) (nth 0%bigQ s k)) (enum 'I_n)).

Definition r_L (l : PP.L) (s : BQP.L) :=
  r_rV l.1 s.1 && r_rV l.2 s.2.

Definition r_U (u : PP.U) (s : BQP.U) :=
  (size s == (PP.m).+1) &&
  all (fun k => r_cV (col k u) (nth [::] s k)) (enum 'I_((PP.m).+1)).

Definition r_Po (PPo : seq PP.L) (BQPo : seq BQP.L) :=
  (size PPo == size BQPo) && all (fun x => r_L x.1 x.2) (zip PPo BQPo).

(*return the transpose to make further computations easier*)

Section Proofs.

Add Relation bigQ BigQ.eq
  reflexivity proved by (@Equivalence_Reflexive _ _ BigQ.eq_equiv)
  symmetry proved by (@Equivalence_Symmetric _ _ BigQ.eq_equiv)
  transitivity proved by (@Equivalence_Transitive _ _ BigQ.eq_equiv)
as bigQ_eq_rel.

Add Parametric Morphism : r with signature eq ==> BigQ.eq ==> eq as r_morph.
Proof. by move=> ????; apply/(sameP idP)/(iffP idP); apply/r_inj => //; symmetry. Qed.


Lemma bigQ_eqP x y: reflect (BigQ.eq x y) (BigQ.eqb x y).
Proof.
rewrite/BigQ.eqb; apply/(iffP idP).
+ exact: BigQ.eqb_correct.
+ exact: BigQ.eqb_complete.
Qed.

Lemma eq_seq_BQ_refl: Reflexive BQP.eq_seq_bigQ.
Proof.
move=> u.
elim: u => // a l ih; rewrite /BQP.eq_seq_bigQ /=; apply/andP; split => //.
exact/bigQ_eqP.
Qed.

Lemma eq_seq_BQ_sym: Symmetric BQP.eq_seq_bigQ.
Proof.
move=> u v.
elim: u v => //=.
- by case.
- move=> a l ih [|b l'] //= /andP [] /bigQ_eqP ? /ih ?; apply/andP.
  by split=> //; apply/bigQ_eqP; symmetry.
Qed.

Lemma eq_seq_BQ_trans: Transitive BQP.eq_seq_bigQ.
Proof.
move=> u v w; elim: v u w.
- by case => //.
- move=> a l ih; case=> // b l'; case => // c l'' /=.
  case/andP=> /bigQ_eqP ba ? /andP [/bigQ_eqP ac ?]; apply/andP; split.
  + exact/bigQ_eqP/(@Equivalence_Transitive _ _ BigQ.eq_equiv b a).
  + exact: ih.
Qed.

Add Relation (seq bigQ) (BQP.eq_seq_bigQ)
  reflexivity proved by eq_seq_BQ_refl
  symmetry proved by eq_seq_BQ_sym
  transitivity proved by eq_seq_BQ_trans
as bigQ_eq_seq_rel.

Lemma eq_seq_BQ_size s1 s2: BQP.eq_seq_bigQ s1 s2 -> size s1 = size s2.
Proof. by elim: s1 s2=> [[]|a l ih []] //= b l' /andP [_ /ih] ->. Qed.

Lemma eq_seq_BQ_nth u v k:
  BQP.eq_seq_bigQ u v -> (nth 0 u k == nth 0 v k)%bigQ.
Proof.
elim: u v k; first by case.
move=> a l ih; case=> // b l' /=; case.
- by case/andP => /bigQ_eqP ? _.
- move=> n /andP [_ ?] /=; exact: ih.
Qed.

Add Parametric Morphism (n : nat) : (@r_rV n)
  with signature eq ==> BQP.eq_seq_bigQ ==> eq as r_rV_morph.
Proof.
move=> y s1 s2 eq_s12; rewrite /r_rV (eq_seq_BQ_size eq_s12); congr andb.
apply: eq_all=> k; move: (eq_seq_BQ_nth k eq_s12); exact: r_morph.
Qed.

Add Parametric Morphism (n : nat) : (@r_cV n)
  with signature eq ==> BQP.eq_seq_bigQ ==> eq as r_cV_morph.
Proof.
move=> y s1 s2 eq_s12; rewrite /r_cV (eq_seq_BQ_size eq_s12); congr andb.
apply: eq_all=> k; move: (eq_seq_BQ_nth k eq_s12); exact: r_morph.
Qed.

Lemma r_rVP {n} (v : 'rV_n) s:
  reflect (size s = n /\ (forall k : 'I_n, r (v 0 k) (nth 0%bigQ s k)))
  (r_rV v s).
Proof.
apply/(iffP idP); rewrite /r_rV.
- case/andP => /eqP -> /allP in_enum; split=> // k; apply: in_enum.
  by apply/(nthP k); exists k; rewrite ?size_enum_ord ?nth_ord_enum.
- case => -> all_In; rewrite eq_refl /=.
  apply/allP => k k_In; exact: all_In.
Qed.

Lemma r_rV0 (v : 'rV_0) s:
  r_rV v s -> s = [::].
Proof. by case/r_rVP => /size0nil. Qed.

Lemma r_rVS {n} (v : 'rV_(n.+1)) c s:
  r_rV v (c :: s) -> r (v 0 0) c /\ exists v' : 'rV_n, r_rV v' s.
Proof.
move=> r_v_cs; split.
- by case/r_rVP : r_v_cs => _ /(_ 0).
- exists (\row_(i < n) v 0 (lift ord0 i)).
  case/r_rVP : r_v_cs => /eqP /=; rewrite eqSS => sizes all_ISn.
  apply/r_rVP; split; first exact/eqP.
  rewrite /=.




Lemma bigQ_dotE n (x : 'rV_n) (y : 'cV_n) (a b : seq bigQ):
  r_rV x a -> r_cV y b ->
  r '[x^T , y] (BQP.bigQ_dot a b).
Proof.
Admitted.

Lemma bigQ_productE (l : PP.L) (u : PP.U) (bl : BQP.L) (bu : BQP.U) :
  r_L l bl -> r_U u bu ->
  r_rV (l.1 *m u) [seq BQP.bigQ_dot bl.1 u0 | u0 <- bu].
Proof.
Admitted.
 

Lemma sat_ineqE (l : PP.L) (u: PP.U) bl bu:
  r_L l bl -> r_U u bu ->
  PP.sat_ineq l u = BQP.sat_ineq bl bu.
Proof.
Admitted.

Lemma sat_eqE (l : PP.L) (u: PP.U) bl bu :
  r_L l bl -> r_U u bu ->
  PP.sat_eq l u = BQP.sat_eq bl bu.
Proof.
Admitted.

Lemma r_Po_nilL BQPo:
  reflect (BQPo = [::]) (r_Po [::] BQPo).
Proof. apply/(iffP idP); [by case: BQPo | by move=> ->]. Qed.

Lemma r_Po_nilR PPo:
  reflect (PPo = [::]) (r_Po PPo [::]).
Proof. apply/(iffP idP); [by case: PPo | by move=> ->]. Qed.

Lemma r_Po_cons PPo BQPo Pc BQc:
  r_Po (Pc :: PPo) (BQc :: BQPo) ->
  [/\ r_L Pc BQc, (size PPo = size BQPo) & (r_Po PPo BQPo)].
Proof. by rewrite /r_Po /= eqSS; case/and3P => /eqP -> -> ->; rewrite eq_refl. Qed. 



Lemma mask_eqE PPo BQPo uP uBQ v:
  r_Po PPo BQPo -> r_U uP uBQ ->
  PA.mask_eq PPo v uP = BQA.mask_eq BQPo v uBQ.
Proof.
move=> + rU.
rewrite /PA.mask_eq /BQA.mask_eq.
elim: PPo BQPo v; first by (move=> ?? /r_Po_nilL ->; rewrite !mask0).
move=> a l ih []; first by move=> ? /r_Po_nilR.
move=> b l' [] //= [] v' /r_Po_cons [r_ab _ r_ll'] /=.
+ rewrite (sat_eqE r_ab rU); congr andb; exact/ih.
+ exact/ih.
Qed.

Lemma sat_PoE PPo BQPo uP uBQ:
  r_Po PPo BQPo -> r_U uP uBQ ->
  PA.sat_Po PPo uP = BQA.sat_Po BQPo uBQ.
Proof.
move=> + rU; rewrite /PA.sat_Po /BQA.sat_Po.
elim: PPo BQPo; first by move=> ? /r_Po_nilL ->.
move=> a l ih []; first by move/r_Po_nilR.
move=> b l' /r_Po_cons [r_ab _ r_ll'] /=.
rewrite (sat_ineqE r_ab rU); congr andb.
exact/ih.
Qed.


Section GraphData.

Variable G1 : PG.t.
Variable G2 : BQG.t.
Context (PPo : seq PP.L) (BQPo : seq BQP.L).

Definition eqd_vtx v := match (PG.label v G1), (BQG.label v G2) with
  |Some lP, Some lBQ => r_U lP lBQ
  |_, _ => false
end.

Definition eqv_data := forall v, PG.mem_vertex v G1 -> BQG.mem_vertex v G2 ->
  eqd_vtx v.

Lemma eqv_data_find v xP xBQ:
  eqv_data ->
  PG.find_vertex v G1 = Some xP -> BQG.find_vertex v G2 = Some xBQ ->
  r_U xP.1 xBQ.1.
Proof.
case: xP xBQ => lP nP [lBQ nBQ] /= eqd PGfind BQGfind.
move: (eqd v (PG.find_mem PGfind) (BQG.find_mem BQGfind)).
rewrite /eqd_vtx /PG.label /BQG.label.
rewrite /PG.find_vertex /BQG.find_vertex in PGfind BQGfind.
by rewrite PGfind BQGfind /=.
Qed.

Lemma eqv_vertex_consistent: (eqv_graph G1 G2) -> eqv_data ->
  r_Po PPo BQPo ->
  PA.vertex_consistent PPo G1 =
  BQA.vertex_consistent BQPo G2.
Proof.
case => eqvtx eqedge eqdata rPo.
rewrite /PA.vertex_consistent /BQA.vertex_consistent.
apply/(sameP idP)/(iffP idP).
- move/BQG.vertex_allP => BQPall; apply/PG.vertex_allP=> v [lP nP] PGfind /=.
  move: (PG.find_mem PGfind); rewrite eqvtx.
  case/BQG.vtx_memE => [[lBQ nBQ]] BQGfind.
  move: (eqv_data_find eqdata PGfind BQGfind) => /= rl.
  rewrite (mask_eqE v rPo rl) (sat_PoE rPo rl).
  exact: (BQPall _ _ BQGfind).
- move/PG.vertex_allP => PGall; apply/BQG.vertex_allP=> v [lBQ nBQ] BQGfind /=.
  move: (BQG.find_mem BQGfind); rewrite -eqvtx.
  case/PG.vtx_memE => [[lP nP]] PGfind.
  move: (eqv_data_find eqdata PGfind BQGfind) => /= rl.
  rewrite -(mask_eqE v rPo rl) -(sat_PoE rPo rl).
  exact: (PGall _ _ PGfind).
Qed.


End GraphData.
End Proofs.

End Refinement.




  







