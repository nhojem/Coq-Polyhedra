From mathcomp Require Import all_ssreflect all_algebra finmap.
From Bignums Require Import BigQ.
Require Import extra_misc inner_product vector_order graph mask.
Require Import Setoid.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory.
Import GRing.Theory Num.Theory.

Open Scope ring_scope.

(* --------------------------------------------------------------------------------------------------- *)

Module Type Prerequisite.

(* L is the type of linear relations,
 * U is the type of "points" (ie vectors or perturbed vectors) *)
Parameters (U L : Type).

Parameters sat_ineq sat_eq: L -> U -> bool.
End Prerequisite.

Module Algorithm (P : Prerequisite).
Import P.

Module Vertex <: Label.
Definition t := U.
End Vertex.

Module O <: MapFold.Sig.
Fact d : unit. Proof. exact: tt. Qed.
Definition T := [orderType of (seqlexi_with d bool)].
End O.

Module AlgoGraph := Graph O Vertex.

Section Body.
Context (n : nat) (Po : seq L) (G : AlgoGraph.t).

Definition sat_Po (x : U) :=
  all (fun e => sat_ineq e x) Po.

Definition mask_eq (m : bitseq) (x : U):=
  all (fun e => sat_eq e x) (mask m Po).

Definition vertex_consistent :=
  let f masq x := mask_eq masq x.1 && sat_Po x.1
  in AlgoGraph.vertex_all G f.

Definition neighbour_condition I :=
  [&& size I == size Po,
      ##|I|  == n,
      AlgoGraph.neighbour_all G (fun J => ##|maskI I J| == (n-1)%nat) I
    & AlgoGraph.nb_neighbours G I == Some n].

Definition struct_consistent :=
  AlgoGraph.vertex_all G (fun I _ => neighbour_condition I).

End Body.
End Algorithm.

Module BigQPrerequisite <: Prerequisite.

Definition U := seq (seq bigQ).

(* e : L is of the form (a, b), with size b = 1 + m, representing the inequality a * x <=_lex b *)
Definition L := (seq bigQ * seq bigQ)%type.

(* TODO: changed foldl into foldr. Mandatory? *)
Definition bigQ_dot (x y : seq bigQ) : bigQ :=
  let aux := (fun p res => BigQ.add_norm res (BigQ.mul_norm p.1 p.2)) in
  foldr aux 0%bigQ (zip x y).

Fixpoint lex_order (x y : seq bigQ) :=
  match x, y with
  | [::], [::] => true
  | hx::tx, hy::ty => match (hx ?= hy)%bigQ with
    | Lt => true
    | Gt => false
    | Eq => lex_order tx ty
    end
  | _, _ => false
  end.

Definition sat_ineq (c : L) (x : U) :=
  let: (a, b) := c in
  let ax := map (fun l => bigQ_dot a l) x in
  lex_order b ax.

Fixpoint eq_seq_bigQ (x y : seq bigQ) :=
  match x, y with
    | [::], [::] => true
    | a::l, b::l' => BigQ.eqb a b && eq_seq_bigQ l l'
    | _, _ => false
  end.

Definition sat_eq (c : L) (x : U) :=
  let: (a, b) := c in
  let ax := map (fun l => bigQ_dot a l) x in
  eq_seq_bigQ ax b.

End BigQPrerequisite.

Module BigQAlgorithm := Algorithm BigQPrerequisite.
Module BQA := BigQAlgorithm.
Module BQG := BigQAlgorithm.AlgoGraph.
Module BQP := BigQPrerequisite.

Section PolySat.

Context (R : realFieldType) (n m: nat).

Definition sat_ineq (l : 'rV[R]_n * 'rV[R]_(S m)) x : bool :=
  (l.1 *m x) >=lex (l.2).
Definition sat_eq (l : 'rV[R]_n * 'rV[R]_(S m)) x : bool :=
  (l.1 *m x) == (l.2).

End PolySat.

Module RatPrerequisite <: Prerequisite.
Parameters (n m : nat).
Definition U := 'M[rat]_(n, m.+1).
Definition L := ('rV[rat]_n * 'rV[rat]_(m.+1))%type.
Definition sat_ineq := @sat_ineq [realFieldType of rat] n m.
Definition sat_eq := @sat_eq [realFieldType of rat] n m.
End RatPrerequisite.

Module RatAlgorithm := Algorithm RatPrerequisite.
Module RatA := RatAlgorithm.
Module RatG := RatAlgorithm.AlgoGraph.
Module RatP := RatPrerequisite.

Section Refinement.

Context (r : rat -> bigQ -> bool).

Hypothesis r_inj : forall x y a b, x = y -> (a == b)%bigQ -> r x a -> r y b.
Hypothesis r_0 : r 0 0%bigQ.
Hypothesis r_mul : forall x y a b, r x a -> r y b ->
  r (x * y) (BigQ.mul_norm a b).
Hypothesis r_add : forall x y a b, r x a -> r y b ->
  r (x + y) (BigQ.add_norm a b).
Hypothesis r_eq : forall x y a b, r x a -> r y b ->
  x = y <-> (a == b)%bigQ.
Hypothesis r_lt: forall x y a b, r x a -> r y b ->
  x < y <-> (a < b)%bigQ.

Definition r_rV (n : nat) (v : 'rV[rat]_n) (s : seq bigQ) :=
  (size s == n) && (all (fun k => r (v 0 k) (nth 0%bigQ s k)) (enum 'I_n)).

Definition r_cV (n : nat) (v : 'cV[rat]_n) (s : seq bigQ) :=
  (size s == n) && (all (fun k => r (v k 0) (nth 0%bigQ s k)) (enum 'I_n)).

Definition r_L (l : RatP.L) (s : BQP.L) :=
  r_rV l.1 s.1 && r_rV l.2 s.2.

Definition r_U (u : RatP.U) (s : BQP.U) :=
  (size s == (RatP.m).+1) &&
  all (fun k => r_cV (col k u) (nth [::] s k)) (enum 'I_((RatP.m).+1)).

Definition r_Po (RatPo : seq RatP.L) (BQPo : seq BQP.L) :=
  (size RatPo == size BQPo) && all (fun x => r_L x.1 x.2) (zip RatPo BQPo).

Section Proofs.

Section ParametricRelations.

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

End ParametricRelations.

Section RefinementProofs.

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

Lemma r_rVnil {n} (v : 'rV_n):
  r_rV v [::] -> n = 0%nat.
Proof. by case/r_rVP => /=. Qed.

Lemma r_rVS {n} (v : 'rV_(n.+1)) c s:
  r_rV v (c :: s) -> r (v 0 0) c /\
  exists2 v' : 'rV_n, r_rV v' s & forall k, v 0 (lift ord0 k) = v' 0 k.
Proof.
move=> r_v_cs; split.
- by case/r_rVP : r_v_cs => _ /(_ 0).
- exists (\row_(i < n) v 0 (lift ord0 i)).
  + case/r_rVP : r_v_cs => /eqP /=; rewrite eqSS => sizes all_ISn.
    apply/r_rVP; split; first exact/eqP.
    move=> k; rewrite mxE; exact:(all_ISn (lift ord0 k)).
  + by move=> k; rewrite mxE.
Qed.

Lemma r_rV_eq {n} (u v: 'rV_n) s t:
  r_rV u s -> r_rV v t -> (u = v <-> BQP.eq_seq_bigQ s t).
Proof.
elim: n s t u v.
- move=> ???? /r_rV0 -> /r_rV0 ->; split=> // _.
  by apply/matrixP=> ? j; move:(ord0_false j).
- move=> n ih; case; first by move=>??? /r_rVnil.
  move=> hs ts; case; first by move=> ?? _ /r_rVnil.
  move=> ht tt u v /r_rVS [r_hs [u' r_u' uu']] /r_rVS [r_ht [v' r_v' vv']].
  rewrite /=; split.
  + move/matrixP => uv; apply/andP; split.
    - exact/bigQ_eqP/(r_eq r_hs r_ht)/uv.
    - apply/(ih _ _ _ _ r_u' r_v')/matrixP=> i j.
      by rewrite (ord1_eq0 i) -uu' -vv' uv.
  + case/andP=> /bigQ_eqP /(r_eq r_hs r_ht) uv0 /(ih _ _ _ _ r_u' r_v').
    move/matrixP=> uv'; apply/rowP=> j.
    case: j=> j jlt.
    move: (@mem_nth _ ord0 (enum 'I_n.+1) (Ordinal jlt)); rewrite size_enum_ord.
    move/(_ jlt); rewrite nth_ord_enum enum_ordS in_cons.
    by case/orP=> [/eqP ->|/mapP [j' j'n ->]] //; rewrite uu' vv'.
Qed.

Lemma r_cVtr {n} (c : 'cV_n) s:
  r_cV c s = r_rV c^T s.
Proof. by rewrite /r_cV /r_rV; congr andb; apply: eq_all => ?; rewrite mxE. Qed.

Lemma r_cVP {n} (v : 'cV_n) s:
  reflect (size s = n /\ (forall k : 'I_n, r (v k 0) (nth 0%bigQ s k)))
  (r_cV v s).
Proof.
rewrite r_cVtr; apply/(iffP (r_rVP v^T s));case=> ? h; split=> // k.
- by move: (h k); rewrite mxE.
- by rewrite mxE.
Qed.

Lemma r_cV0 (v : 'cV_0) s:
  r_cV v s -> s = [::].
Proof. rewrite r_cVtr; exact: r_rV0. Qed.

Lemma r_cVnil {n} (v : 'cV_n):
  r_cV v [::] -> n = 0%nat.
Proof. by case/r_cVP => /=. Qed.


Lemma r_cVS {n} (v : 'cV_(n.+1)) c s:
  r_cV v (c :: s) -> r (v 0 0) c /\
  exists2 v' : 'cV_n, r_cV v' s & forall k, v (lift ord0 k) 0 = v' k 0.
Proof.
rewrite r_cVtr; case/r_rVS; rewrite mxE => -> [v' r_rV' v_k]; split=> //.
exists v'^T; rewrite ?r_cVtr ?trmxK //.
by move=> k; rewrite mxE -v_k mxE.
Qed.

Lemma r_LP (e : RatP.L) (s : BQP.L):
  reflect (r_rV e.1 s.1 /\ r_rV e.2 s.2) (r_L e s).
Proof. exact/andP. Qed.

Lemma r_UP (x : RatP.U) (s : BQP.U):
  reflect
  ((size s = (RatP.m).+1) /\ forall k, r_cV (col k x) (nth [::] s k))
  (r_U x s).
Proof.
apply/(iffP idP); rewrite /r_U.
- case/andP => /eqP -> /allP in_xs; split=> // k; apply: in_xs.
  by apply/(nthP k); exists k; rewrite ?size_enum_ord ?nth_ord_enum.
- case=> -> in_xs; rewrite eq_refl /=; apply/allP=> k k_ord; exact: in_xs.
Qed.

End RefinementProofs.

Section AlgorithmEquiv.

(* TODO: the following lemma is not natural, and makes use of
 * inner_product.v which is unexpected.
 * It should be removed, and the proof of the next lemma should be rewritten accordingly *)
Lemma bigQ_dotE n (x : 'rV_n) (y : 'cV_n) (a b : seq bigQ):
  r_rV x a -> r_cV y b ->
  r '[x^T , y] (BQP.bigQ_dot a b).
Proof.
rewrite /BQP.bigQ_dot.
elim: n x y a b.
- by move=> x y a b /r_rV0 -> /r_cV0 -> /=; rewrite /vdot big_ord0.
- move=> n ih x y; case => [|ha ta]; first by move=> ? /r_rVnil.
  case=> [|hb tb]; first by move=> _ /r_cVnil.
  case/r_rVS=> r_ha [x' r_ta xx'].
  case/r_cVS=> r_hb [y' r_tb yy'].
  rewrite /= /vdot big_ord_recl addrC.
  apply: r_add; rewrite ?mxE ?r_mul //=.
  suff ->: \sum_(i < n) x^T (lift ord0 i) 0 * y (lift ord0 i) 0 =
    '[x'^T, y'] by exact: ih.
  by rewrite /vdot; apply: eq_big => //= i _; rewrite !mxE xx' yy'.
Qed.

Lemma bigQ_productE (l : RatP.L) (u : RatP.U) (bl : BQP.L) (bu : BQP.U) :
  r_L l bl -> r_U u bu ->
  r_rV (l.1 *m u) [seq BQP.bigQ_dot bl.1 u0 | u0 <- bu].
Proof.
case/r_LP=> r_l1 r_l2 /r_UP [size_u r_u]; apply/r_rVP; split.
- by rewrite size_map.
- move=> k; rewrite (nth_map [::]) ?size_u // /mulmx mxE.
  suff ->: \sum_j l.1 0 j * u j k = '[l.1^T, col k u] by exact: bigQ_dotE.
  by apply: eq_big=> // ? _; rewrite !mxE.
Qed.

Lemma bigQ_lexE {n} (u v : 'rV_n) p q:
  r_rV u p -> r_rV v q -> (u <=lex v) = BQP.lex_order p q.
Proof.
elim: n u v p q.
- move=> ???? /r_rV0 -> /r_rV0 -> /=; apply: lex_lev.
  by move=> j; move: (ord0_false j).
- move=> n ih u v; case; first by move=> ? /r_rVnil.
  move=> hp tp; case; first by move=> ? /r_rVnil.
  move=> hq tq /= /r_rVS [r_hp [u' r_tp uu']] /r_rVS [r_hq [v' r_tq vv']].
  case: (BigQ.compare_spec hp hq).
  + move=> eq_hpq; rewrite -(ih u' v') // /leqlex enum_ordS /= lt_neqAle.
    have -> /=: (u 0 ord0 == v 0 ord0) by exact/eqP/(r_eq r_hp r_hq).
    elim: (enum 'I_n) => //= a l ih_eq.
    by rewrite uu' vv' ih_eq.
  + move=> ?; rewrite /leqlex enum_ordS /=.
    suff ->: u 0 ord0 < v 0 ord0 by [].
    exact/(r_lt r_hp r_hq).
  + move=> ?; rewrite /leqlex enum_ordS /=.
    suff lt_vu0: v 0 ord0 < u 0 ord0.
    - by rewrite (lt_gtF lt_vu0) eq_sym (lt_eqF lt_vu0).
    exact/(r_lt r_hq r_hp).
Qed.

Lemma sat_ineqE (l : RatP.L) (u: RatP.U) bl bu:
  r_L l bl -> r_U u bu ->
  RatP.sat_ineq l u = BQP.sat_ineq bl bu.
Proof.
move=> rl ru; move: (bigQ_productE rl ru).
case: l rl ru; case: bl => ???? /r_LP /= [rL1 rL2] rU /= r_prod.
(* rewrite /RatP.sat_ineq /BQP.sat_ineq /sat_ineq /=. *)
exact: bigQ_lexE.
Qed.

Lemma sat_eqE (l : RatP.L) (u: RatP.U) bl bu :
  r_L l bl -> r_U u bu ->
  RatP.sat_eq l u = BQP.sat_eq bl bu.
Proof.
case: l; case: bl=> a b a0 b0 r_l r_u.
move: (bigQ_productE r_l r_u)=> /= r_prod.
case/r_LP: (r_l) => /= _ r_b.
(* rewrite /RatP.sat_eq /BQP.sat_eq /sat_eq /=. *)
apply/(sameP idP)/(iffP idP).
- move=> ?; exact/eqP/(r_rV_eq r_prod r_b).
- move/eqP=> ?; exact/(r_rV_eq r_prod r_b).
Qed.

Lemma r_Po_nilL BQPo:
  reflect (BQPo = [::]) (r_Po [::] BQPo).
Proof. apply/(iffP idP); [by case: BQPo | by move=> ->]. Qed.

Lemma r_Po_nilR RatPo:
  reflect (RatPo = [::]) (r_Po RatPo [::]).
Proof. apply/(iffP idP); [by case: RatPo | by move=> ->]. Qed.

Lemma r_Po_cons RatPo BQPo Pc BQc:
  r_Po (Pc :: RatPo) (BQc :: BQPo) ->
  [/\ r_L Pc BQc, (size RatPo = size BQPo) & (r_Po RatPo BQPo)].
Proof. by rewrite /r_Po /= eqSS; case/and3P => /eqP -> -> ->; rewrite eq_refl. Qed.

Lemma mask_eqE RatPo BQPo uP uBQ v:
  r_Po RatPo BQPo -> r_U uP uBQ ->
  RatA.mask_eq RatPo v uP = BQA.mask_eq BQPo v uBQ.
Proof.
move=> + rU.
rewrite /RatA.mask_eq /BQA.mask_eq.
elim: RatPo BQPo v; first by (move=> ?? /r_Po_nilL ->; rewrite !mask0).
move=> a l ih []; first by move=> ? /r_Po_nilR.
move=> b l' [] //= [] v' /r_Po_cons [r_ab _ r_ll'] /=.
+ rewrite (sat_eqE r_ab rU); congr andb; exact/ih.
+ exact/ih.
Qed.

Lemma sat_PoE RatPo BQPo uP uBQ:
  r_Po RatPo BQPo -> r_U uP uBQ ->
  RatA.sat_Po RatPo uP = BQA.sat_Po BQPo uBQ.
Proof.
move=> + rU; rewrite /RatA.sat_Po /BQA.sat_Po.
elim: RatPo BQPo; first by move=> ? /r_Po_nilL ->.
move=> a l ih []; first by move/r_Po_nilR.
move=> b l' /r_Po_cons [r_ab _ r_ll'] /=.
rewrite (sat_ineqE r_ab rU); congr andb.
exact/ih.
Qed.

Section GraphStructure.

Variable n : nat.
Variable G1 : RatG.t.
Variable G2 : BQG.t.
Context (RatPo : seq RatP.L) (BQPo : seq BQP.L).

Definition eqv_graph :=
  (RatG.mem_vertex G1 =1 BQG.mem_vertex G2) /\
  (RatG.mem_edge G1 =2 BQG.mem_edge G2).

Lemma perm_eqv_graph: eqv_graph ->
  perm_eq (RatG.vertex_list G1) (BQG.vertex_list G2).
Proof.
rewrite /RatG.adj_list /BQG.adj_list.
case=> ? _; apply: uniq_perm; rewrite ?RatG.MF.uniq_keys ?BQG.MF.uniq_keys //.
by move=> v; rewrite RatG.vtx_mem_list BQG.vtx_mem_list.
Qed.

Lemma eqv_struct_consistent : eqv_graph -> r_Po RatPo BQPo ->
  RatA.struct_consistent n RatPo G1 = BQA.struct_consistent n BQPo G2.
Proof.
move=> [eqvtx eqedg] rPo; rewrite /RatA.struct_consistent /BQA.struct_consistent.
rewrite (RatG.vertex_all_eq _ (RatG.adj_listP G1)).
rewrite (BQG.vertex_all_eq _ (BQG.adj_listP G2)) -!all_map.
rewrite (@eq_all _ (RatA.neighbour_condition n RatPo G1) (BQA.neighbour_condition n BQPo G2)).
  exact/perm_all/perm_eqv_graph.
move=> I; rewrite /RatA.neighbour_condition /BQA.neighbour_condition.
congr andb; first by case/andP: rPo=> /eqP ->.
congr andb.
case E: (RatG.mem_vertex G1 I).
- rewrite (@RatG.neighbour_all_eq _ _ _ (RatG.neighbour_list G1 I)) //.
  rewrite eqvtx in E.
  rewrite (@BQG.neighbour_all_eq _ _ _ (BQG.neighbour_list G2 I)) //.
  have perm_nei: perm_eq (RatG.neighbour_list G1 I) (BQG.neighbour_list G2 I).
  + apply/uniq_perm; rewrite ?RatG.uniq_neighbour_list ?BQG.uniq_neighbour_list //.
    by move=> x; rewrite -RatG.edge_mem_list -BQG.edge_mem_list eqedg.
  congr (_ && _); first exact/perm_all.
  + rewrite (RatG.nb_neighbours_list) ?(BQG.nb_neighbours_list) ?eqvtx //.
    by rewrite (perm_size perm_nei).
  + rewrite RatG.neighbour_allF ?BQG.neighbour_allF -?eqvtx ?E //=.
    by rewrite RatG.nb_neighboursF ?BQG.nb_neighboursF -?eqvtx ?E.
Qed.

End GraphStructure.

Section GraphData.
Variable G1 : RatG.t.
Variable G2 : BQG.t.
Context (RatPo : seq RatP.L) (BQPo : seq BQP.L).

Definition eqd_vtx v := match (RatG.label G1 v), (BQG.label G2 v) with
  |Some lP, Some lBQ => r_U lP lBQ
  |_, _ => false
end.

Definition eqv_data := forall v, RatG.mem_vertex G1 v -> BQG.mem_vertex G2 v ->
  eqd_vtx v.

Lemma eqv_data_find v xP xBQ:
  eqv_data ->
  RatG.find_vertex G1 v = Some xP -> BQG.find_vertex G2 v = Some xBQ ->
  r_U xP.1 xBQ.1.
Proof.
case: xP xBQ => lP nP [lBQ nBQ] /= eqd RatGfind BQGfind.
move: (eqd v (RatG.find_mem RatGfind) (BQG.find_mem BQGfind)).
rewrite /eqd_vtx /RatG.label /BQG.label.
rewrite /RatG.find_vertex /BQG.find_vertex in RatGfind BQGfind.
by rewrite /RatG.find_vertex /BQG.find_vertex RatGfind BQGfind /=.
Qed.

Lemma eqv_vertex_consistent: (eqv_graph G1 G2) -> eqv_data ->
  r_Po RatPo BQPo ->
  RatA.vertex_consistent RatPo G1 = BQA.vertex_consistent BQPo G2.
Proof.
case => eqvtx eqedge eqdata rPo.
rewrite /RatA.vertex_consistent /BQA.vertex_consistent.
apply/(sameP idP)/(iffP idP).
- move/BQG.vertex_allP => BQPall; apply/RatG.vertex_allP=> v [lP nP] RatGfind /=.
  move: (RatG.find_mem RatGfind); rewrite eqvtx.
  case/BQG.vtx_memE => [[lBQ nBQ]] BQGfind.
  move: (eqv_data_find eqdata RatGfind BQGfind) => /= rl.
  rewrite (mask_eqE v rPo rl) (sat_PoE rPo rl).
  exact: (BQPall _ _ BQGfind).
- move/RatG.vertex_allP => RatGall; apply/BQG.vertex_allP=> v [lBQ nBQ] BQGfind /=.
  move: (BQG.find_mem BQGfind); rewrite -eqvtx.
  case/RatG.vtx_memE => [[lP nP]] RatGfind.
  move: (eqv_data_find eqdata RatGfind BQGfind) => /= rl.
  rewrite -(mask_eqE v rPo rl) -(sat_PoE rPo rl).
  exact: (RatGall _ _ RatGfind).
Qed.

End GraphData.
End AlgorithmEquiv.
End Proofs.

End Refinement.

(* Section TestExtract.

Local Open Scope bigQ_scope.

Definition Po: seq (seq bigQ * seq bigQ) := [::
   ([:: -1; 0; 0], [::1; 1; 0; 0; 0; 0; 0])
;  ([:: 0; -1; 0], [::1; 0; 1; 0; 0; 0; 0])
;  ([:: 0; 0; -1], [::1; 0; 0; 1; 0; 0; 0])
;  ([:: 1; 0; 0], [::1; 0; 0; 0; 1; 0; 0])
;  ([:: 0; 0; 1], [::1; 0; 0; 0; 0; 1; 0])
;  ([:: 0; 1; 0], [::1; 0; 0; 0; 0; 0; 1])
].

Definition m : nat := 6%N.
Definition n : nat := 3%N.

Definition v_data_0000 : seq (bitseq * (seq (seq bigQ))) := [::
   ([:: false; false; false; true; true; true], [::
  [:: 1; 1; 1 ]
; [:: 0; 0; 0 ]
; [:: 0; 0; 0 ]
; [:: 0; 0; 0 ]
; [:: 1; 0; 0 ]
; [:: 0; 0; 1 ]
; [:: 0; 1; 0 ]
])
;  ([:: true; false; false; false; true; true], [::
  [:: -1; 1; 1 ]
; [:: -1; 0; 0 ]
; [:: 0; 0; 0 ]
; [:: 0; 0; 0 ]
; [:: 0; 0; 0 ]
; [:: 0; 0; 1 ]
; [:: 0; 1; 0 ]
])
;  ([:: false; false; true; true; false; true], [::
  [:: 1; 1; -1 ]
; [:: 0; 0; 0 ]
; [:: 0; 0; 0 ]
; [:: 0; 0; -1 ]
; [:: 1; 0; 0 ]
; [:: 0; 0; 0 ]
; [:: 0; 1; 0 ]
])
;  ([:: true; false; true; false; false; true], [::
  [:: -1; 1; -1 ]
; [:: -1; 0; 0 ]
; [:: 0; 0; 0 ]
; [:: 0; 0; -1 ]
; [:: 0; 0; 0 ]
; [:: 0; 0; 0 ]
; [:: 0; 1; 0 ]
])
;  ([:: false; true; true; true; false; false], [::
  [:: 1; -1; -1 ]
; [:: 0; 0; 0 ]
; [:: 0; -1; 0 ]
; [:: 0; 0; -1 ]
; [:: 1; 0; 0 ]
; [:: 0; 0; 0 ]
; [:: 0; 0; 0 ]
])
;  ([:: true; true; true; false; false; false], [::
  [:: -1; -1; -1 ]
; [:: -1; 0; 0 ]
; [:: 0; -1; 0 ]
; [:: 0; 0; -1 ]
; [:: 0; 0; 0 ]
; [:: 0; 0; 0 ]
; [:: 0; 0; 0 ]
])
;  ([:: false; true; false; true; true; false], [::
  [:: 1; -1; 1 ]
; [:: 0; 0; 0 ]
; [:: 0; -1; 0 ]
; [:: 0; 0; 0 ]
; [:: 1; 0; 0 ]
; [:: 0; 0; 1 ]
; [:: 0; 0; 0 ]
])
;  ([:: true; true; false; false; true; false], [::
  [:: -1; -1; 1 ]
; [:: -1; 0; 0 ]
; [:: 0; -1; 0 ]
; [:: 0; 0; 0 ]
; [:: 0; 0; 0 ]
; [:: 0; 0; 1 ]
; [:: 0; 0; 0 ]
])
].

Definition e_data_0000 : seq (bitseq * bitseq) := [::
  ([:: true; false; false; false; true; true], [:: false; false; false; true; true; true])
; ([:: false; false; true; true; false; true], [:: false; false; false; true; true; true])
; ([:: true; false; true; false; false; true], [:: false; false; true; true; false; true])
; ([:: true; false; true; false; false; true], [:: true; false; false; false; true; true])
; ([:: false; true; true; true; false; false], [:: false; false; true; true; false; true])
; ([:: true; true; true; false; false; false], [:: false; true; true; true; false; false])
; ([:: true; true; true; false; false; false], [:: true; false; true; false; false; true])
; ([:: false; true; false; true; true; false], [:: false; false; false; true; true; true])
; ([:: false; true; false; true; true; false], [:: false; true; true; true; false; false])
; ([:: true; true; false; false; true; false], [:: false; true; false; true; true; false])
; ([:: true; true; false; false; true; false], [:: true; false; false; false; true; true])
; ([:: true; true; false; false; true; false], [:: true; true; true; false; false; false])
].

Definition G := Eval native_compute in BigQAlgorithm.AlgoGraph.empty.


Definition G_0 :=  Eval native_compute in BigQAlgorithm.AlgoGraph.add_vertices v_data_0000 G.
Definition H_0 := BigQAlgorithm.AlgoGraph.add_edges e_data_0000 G_0.
Definition input := Eval native_compute in H_0.

Definition vtx_output :=
  Eval native_compute in bigQ_vtx_consistent Po input.

Definition struct_output :=
    Eval native_compute in bigQ_struct_consistent n input.

Print vtx_output.
Print struct_output.

End TestExtract. *)
