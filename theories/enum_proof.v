From mathcomp Require Import all_ssreflect all_algebra finmap.
Require Import extra_misc inner_product extra_matrix vector_order.
Require Import lrel polyhedron poly_base.
Require Import mask enum_algo graph high_graph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory.
Import GRing.Theory Num.Theory.

Open Scope ring_scope.

Section Perturbation.

Context (n m: nat) (R: realFieldType) (base : m.-tuple lrel[R]_n).
Definition plrel := ('rV[R]_n * 'rV[R]_(m.+1))%type.

Definition create_perturbation (b : R) (k : 'I_m) : 'rV_(m.+1) :=
  @row_mx _ _ 1 m b%:M (- delta_mx 0 k).

Definition perturbation_seq : seq plrel :=
  map
  (fun x: lrel[R]_n * 'I_m => (x.1.1^T , create_perturbation x.1.2 x.2))
  (zip base (enum 'I_m)).

Program Definition perturbation := @Tuple m _ perturbation_seq _.
Next Obligation.
Proof. by rewrite size_map size_zip size_tuple size_enum_ord minnn. Qed.

Lemma nth_pert (i : 'I_m) : perturbation`_ i = ((base`_ i).1^T , (row_mx (base`_ i).2%:M (- delta_mx 0 i))).
Proof.
rewrite (nth_map (lrel0, i)) /= ?size_zip ?size_enum_ord ?size_tuple ?minnn //.
rewrite !nth_zip ?size_enum_ord ?size_tuple //=; congr pair.
by rewrite nth_ord_enum.
Qed.

(* Definition zero_pert_seq : seq plrel := [seq (x.1^T , row_mx x.2%:M 0) | x : lrel[R]_n <- base].
Program Definition zero_pert := @Tuple m _ zero_pert_seq _.
Next Obligation. Proof. by rewrite size_map size_tuple. Qed. *)

End Perturbation.


Section LexiBasis.

Context (R : realFieldType) (n m : nat).
Context (base : m.-tuple (plrel n m R)).

Lemma mxsub_scalar_mx (p q : nat) (f : 'I_p -> 'I_q) (a : R) :
  injective f -> mxsub f f (a%:M) = a%:M.
Proof. by move=> f_inj; apply/matrixP=> i j; rewrite !mxE (inj_eq f_inj). Qed.

Definition lhs_base := unzip1 base.
Definition rhs_base := unzip2 base.

Record lexi_prebasis := Lexi {
  s :> m.-choose n;
  _ : basis_of fullv (mask s lhs_base);
  }.

Canonical lexipre_subType := Eval hnf in [subType for s].
Definition lexipre_eqMixin := [eqMixin of lexi_prebasis by <:].
Canonical lexipre_eqType := EqType _ lexipre_eqMixin.
Definition lexipre_choiceMixin := [choiceMixin of lexi_prebasis by <:].
Canonical lexipre_choiceType := ChoiceType _ lexipre_choiceMixin.
Definition lexipre_countMixin := [countMixin of lexi_prebasis by <:].
Canonical lexipre_countType := CountType _ lexipre_countMixin.
Canonical lexipre_subCountType := [subCountType of lexi_prebasis].
Definition lexipre_finMixin := [finMixin of lexi_prebasis by <:].
Canonical lexipre_finType := FinType _ lexipre_finMixin.

Lemma lexi_vbasis (L : lexi_prebasis) : basis_of fullv (mask L lhs_base).
Proof. by case: L => ? /=. Qed.

Definition lhs_mat := \matrix_(i < m) lhs_base`_i : 'M_(m, n).
Definition rhs_mat := \matrix_(i < m) rhs_base`_i.

Definition mask_lhs (L : m.-choose n) : 'M_n :=
  rowsub (fmask_nth L) lhs_mat.

Definition mask_rhs (L :  m.-choose n) : 'M_(n, m.+1) :=
  rowsub (fmask_nth L) rhs_mat.

Lemma mask_lhsE (L : m.-choose n) (i : 'I_n) :
  row i (mask_lhs L) = (mask L lhs_base)`_i.
Proof. by rewrite row_rowsub rowK fmask_nthP. Qed.

Lemma mask_rhsE (L : m.-choose n) (i : 'I_n) :
  row i (mask_rhs L) = (mask L rhs_base)`_i.
Proof. by rewrite row_rowsub rowK fmask_nthP. Qed.

Lemma mask_baseE (L : m.-choose n) (i : 'I_n) :
  (row i (mask_lhs L), row i (mask_rhs L)) = (mask L base)`_i.
Proof.
rewrite mask_lhsE mask_rhsE -!map_mask.
rewrite !(nth_map 0) ?size_mask ?card_fmask ?size_fmask ?size_tuple //.
by case: ((mask L base)`_i).
Qed.

Lemma mtx_vbasisE (L : m.-choose n) :
  reflect (basis_of fullv (mask L lhs_base)) (mask_lhs L \in unitmx).
Proof.
rewrite -row_full_unit; apply/(iffP idP).
- rewrite basisEdim size_mask ?size_tuple //.
  rewrite card_fmask dimvf /Vector.dim /= mul1n leqnn andbT.
  case/row_fullP => B Bdef; apply/subvP=> /= x _.
  move/(congr1 (mulmx x)): Bdef; rewrite mulmx1 => <-.
  rewrite mulmxA mulmx_sum_row.
  apply: memv_suml => /= i _; apply: memvZ.
  (* TODO : ugly, need lemma *)
  by rewrite mask_lhsE memv_span // mem_nth ?size_mask ?card_fmask ?size_fmask ?size_map ?size_tuple.
- move/span_basis/vspaceP => h_span.
  rewrite -sub1mx; apply/rV_subP => v _.
  move: (h_span v); rewrite memvf.
  have size_n : size (mask L lhs_base) == n by rewrite size_mask ?card_fmask ?size_fmask ?size_map ?size_tuple.
  have -> : <<mask L lhs_base>>%VS = << Tuple size_n >>%VS by exact/eq_span.
  move/coord_span => /= ->; apply/summx_sub=> i _; apply/scalemx_sub.
  by rewrite -mask_lhsE row_sub.
Qed.

Lemma lexi_matrix_inv (L : lexi_prebasis) : (mask_lhs L) \in unitmx.
Proof. exact/mtx_vbasisE/lexi_vbasis. Qed.

Definition lexi_point (L : lexi_prebasis) : 'M_(n, m.+1) :=
  (invmx (mask_lhs L)) *m (mask_rhs L).

(* ---------------------------------------------------------------------------- *)

Definition all_sat (x : 'M[R]_(n,m.+1)) :=
  all (fun l => sat_ineq l x) base.

Definition sat_mask (mas : bitseq) (x : 'M[R]_(n, m.+1)) :=
  all (fun l => sat_ineq l x) (mask mas base).

Definition eq_mask (mas : bitseq) (x : 'M[R]_(n, m.+1)) :=
  all (fun l => sat_eq l x) (mask mas base).

(* TODO : lex order for matrices by line *)
Lemma prelexi_sat_point x :
  all_sat x -> forall i, (row i (lhs_mat *m x)) >=lex (row i rhs_mat).
Proof.
move/allP => /= satx i.
rewrite row_mul !rowK !(nth_map 0) ?size_tuple //.
by apply/satx/mem_nth; rewrite size_tuple.
Qed.

Lemma prelexi_mask_point (L : m.-choose n) x :
  eq_mask L x ->
  (mask_lhs L) *m x = (mask_rhs L).
Proof.
move=> /allP /= eqx.
apply/row_matrixP => i.
rewrite row_mul mask_lhsE mask_rhsE -!map_mask.
rewrite !(nth_map 0) ?size_mask ?card_fmask ?size_fmask ?size_tuple //.
apply/eqP/eqx/mem_nth.
by rewrite ?size_mask ?card_fmask ?size_fmask ?size_tuple.
Qed.

Record lexi_basis := Lexb
{
  sb :> lexi_prebasis;
  _ : all_sat (lexi_point sb)
}.

Canonical lexi_subType := Eval hnf in [subType for sb].
Definition lexi_eqMixin := [eqMixin of lexi_basis by <:].
Canonical lexi_eqType := EqType _ lexi_eqMixin.
Definition lexi_choiceMixin := [choiceMixin of lexi_basis by <:].
Canonical lexi_choiceType := ChoiceType _ lexi_choiceMixin.
Definition lexi_countMixin := [countMixin of lexi_basis by <:].
Canonical lexi_countType := CountType _ lexi_countMixin.
Canonical lexi_subCountType := [subCountType of lexi_basis].
Definition lexi_finMixin := [finMixin of lexi_basis by <:].
Canonical lexi_finType := FinType _ lexi_finMixin.

Lemma lexi_sat (L : lexi_basis) : all_sat (lexi_point L).
Proof. by case: L. Qed.

Lemma lexi_eq (L : lexi_basis) : eq_mask L (lexi_point L).
Proof.
apply/allP => /= e /nthP /= /(_ 0) [i].
rewrite size_mask ?size_tuple // card_fmask=> i_ord <-.
set i' := Ordinal i_ord.
rewrite -(mask_baseE _ i') /lexi_point /sat_eq mulmxA /=.
by rewrite -row_mul mulmxV ?lexi_matrix_inv // -row_mul mul1mx.
Qed.

Definition lexi_graph :=
  mk_graph [fset L | L : lexi_basis]
    (fun L1 L2 => ##| maskI L1 L2 | == (n-1)%N).

Definition lexi_mask_graph :=
  (fun x : lexi_basis => x : bitseq) @° lexi_graph.

Lemma lexi_giso : giso lexi_graph lexi_mask_graph.
Proof.
exists (fun x : lexi_basis => x : bitseq); split=> // ?? _ _.
by do 4! move/val_inj.
Qed.

Lemma lexi_regular : regular lexi_graph n.
Proof. Admitted.

Lemma lexi_connected : connected lexi_graph.
Proof. Admitted.

End LexiBasis.

Section RelGraph.

Let n := RatP.n.
Let m := RatP.m.
Context (base : m.-tuple lrel[rat]_n).
Context (g : RatG.t).


Definition target_Po := perturbation base.
Definition target_graph := lexi_mask_graph target_Po.

(* TODO: add the nonemptiness test of g in struct_consistent *)
Hypothesis g_struct : RatA.struct_consistent n target_Po g.
Hypothesis g_vtx : RatA.vertex_consistent target_Po g.

Definition computed_graph := mk_graph [fset x | x in RatG.vertex_list g] (RatG.mem_edge g).

Lemma cgraph_neq0 : computed_graph != (graph0 _).
Proof.
case/andP : g_struct; rewrite RatG.empty_vtx_list => vtx_list_n0 _.
apply/graph0Pn; rewrite vtx_mk_graph; apply/fset0Pn.
move: vtx_list_n0; apply/contra_neq.
case : (RatG.vertex_list g)=> // ?? /eqP /=.
by rewrite fset_cons fsetU_eq0 -cardfs_eq0 cardfs1.
Qed.

Definition low_point k := if RatG.label g k is Some l then l else 0.

Section LowPointIng.

Context (k : bitseq).
Hypothesis k_mem : RatG.mem_vertex g k.

Lemma mem_low_size: size k == m.
Proof.
case/andP: g_struct => _ /RatG.vertex_allP H.
case/RatG.vtx_memE: k_mem=> e /H/and4P [].
by rewrite size_tuple.
Qed.

Definition kt := Tuple mem_low_size.

Lemma mem_low_card: ##|kt| == n.
Proof.
case/andP: g_struct => _ /RatG.vertex_allP H.
by case/RatG.vtx_memE: k_mem=> e /H/and4P [].
Qed.

Definition km := CMask mem_low_card.

Lemma low_pointP:
  exists2 e, RatG.find_vertex g km = Some e & e.1 = low_point km.
Proof.
move: k_mem=> /RatG.vtx_memE [].
by rewrite /low_point /RatG.label; case=> a b ->; exists (a,b).
Qed.

Lemma mem_low_sat:
  all_sat target_Po (low_point km).
Proof.
move/RatG.vertex_allP: g_vtx low_pointP => H [e].
by case/H/andP => _ ? <-.
Qed.

Lemma mem_low_mask:
  eq_mask target_Po km (low_point km).
Proof.
move/RatG.vertex_allP: g_vtx low_pointP => H [e].
by case/H/andP => ? _ <-.
Qed.

Lemma low_mtx_affP:
  (mask_lhs target_Po km) *m (low_point km) = (mask_rhs target_Po km).
Proof. exact/prelexi_mask_point/mem_low_mask. Qed.

(* Lemma col'_mul {R : realFieldType} {p q r : nat}
  (M : 'M[R]_(p,q)) (N : 'M[R]_(q,r)) j: col' j (M *m N) = M *m (col' j N).
Proof.
by rewrite !col'Esub mulmx_colsub.
Qed. *)

Lemma target_Po_lift : colsub (lift 0) (rhs_mat target_Po) = -1%:M.
Proof.
apply/matrixP=> i j /=.
rewrite !mxE (nth_map 0) ?size_tuple //.
rewrite nth_pert /= -rshift1.
by rewrite (@row_mxEr _ 1 1) !mxE eq_refl /= eq_sym.
Qed.

Lemma col_maskP :
  (mask_lhs target_Po km) *m colsub ((lift 0) \o fmask_nth km) (low_point km) = -1%:M.
Proof.
rewrite mulmx_colsub low_mtx_affP colsub_comp -mxsubcr.
rewrite [X in colsub _ X]mxsubrc target_Po_lift -mxsubcr.
apply/matrixP=> i j; rewrite !mxE; congr (_ *- _).
rewrite inj_eq //; exact/fmask_nth_inj.
Qed.

Definition extr_low_point := - colsub ((lift 0) \o fmask_nth km) (low_point km).

Lemma extr_low_pointE : (mask_lhs target_Po km) *m extr_low_point = 1%:M.
Proof. by rewrite mulmxN col_maskP opprK. Qed.

Lemma extr_low_inv : (mask_lhs target_Po km) \in unitmx.
Proof. by case/mulmx1_unit: extr_low_pointE. Qed.

Lemma low_vbasis: basis_of fullv (mask km (lhs_base target_Po)).
Proof. exact/mtx_vbasisE/extr_low_inv. Qed.

Definition low_prebasis := Lexi low_vbasis.

Lemma low_lexipoint : lexi_point low_prebasis = low_point km.
Proof.
apply: (@row_full_inj _ _ _ _ (mask_lhs target_Po km)).
- by rewrite row_full_unit extr_low_inv.
- by rewrite mulKVmx ?extr_low_inv // low_mtx_affP.
Qed.

Lemma low_presat : all_sat target_Po (lexi_point low_prebasis).
Proof. by rewrite low_lexipoint mem_low_sat. Qed.

Definition low_lexibasis := Lexb low_presat.

Lemma mem_foo: k \in vertices target_graph.
Proof.
rewrite vtx_img_graph vtx_mk_graph; apply/imfsetP.
by exists low_lexibasis; rewrite ?in_imfset.
Qed.

End LowPointIng.

Section StructCons.

Lemma low_edge x y: RatG.mem_edge g x y -> ##| maskI x y| == (n - 1)%nat.
Proof.
  case/andP: g_struct => _ /RatG.vertex_allP vtx_cond.
rewrite RatG.edge_mem_list => y_nei_x.
have: RatG.neighbour_list g x != [::] by
  move: y_nei_x; case: (RatG.neighbour_list g x).
move/RatG.neighbour_list_mem => /[dup] xg /RatG.vtx_memE [e] /vtx_cond.
case/and4P=> _ _ /RatG.neighbour_allP.
by case/(_ xg _ y_nei_x)/andP.
Qed.

Lemma edge_target : {in vertices computed_graph &, forall x y,
  edges computed_graph x y -> edges target_graph x y}.
Proof.
move=> x y; rewrite vtx_mk_graph !inE /= !RatG.vtx_mem_list=> xVc yVc.
rewrite edge_mk_graph ?inE ?RatG.vtx_mem_list //.
move=> xgy; apply/edge_img_graph.
exists (low_lexibasis xVc); exists (low_lexibasis yVc); split=> //=.
rewrite edge_mk_graph ?inE //=.
exact:low_edge.
Qed.

Lemma computed_succ_card :
  {in vertices computed_graph, forall x, (n <= #|` successors computed_graph x |)%nat}.
Proof.
move=> x; rewrite vtx_mk_graph inE /= RatG.vtx_mem_list=> /[dup] xg.
rewrite RatG.vtx_memE => -[e xg_is_e].
case/andP: g_struct => _ /RatG.vertex_allP /(_ _ _ xg_is_e).
case/and4P=> _ _.
rewrite (RatG.neighbour_all_eq _ xg (perm_refl _)).
move/allP=> h_nei.
rewrite succ_mk_graph ?inE ?RatG.vtx_mem_list //.
rewrite RatG.nb_neighbours_list // => /eqP/Some_inj <-.
rewrite card_imfset //=.
apply: uniq_leq_size; first exact: RatG.uniq_neighbour_list.
move=> y /[dup] /h_nei /andP [_ yg]; rewrite -RatG.edge_mem_list => xgy.
by rewrite mem_filter inE /= xgy RatG.vtx_mem_list yg.
Qed.

Lemma low_succE : {in vertices computed_graph, forall x,
  successors computed_graph x = successors target_graph x}.
Proof.
move=> x xV1; apply/eqP; rewrite eqEfcard; apply/andP; split.
- apply/fsubsetP=> y; rewrite !in_succE=> /[dup] /edge_vtxr yV1.
  exact:(edge_target).
- rewrite (giso_regular (n:=n) (lexi_giso _)) ?computed_succ_card //.
  + exact: lexi_regular.
  + rewrite vtx_mk_graph inE RatG.vtx_mem_list in xV1.
    rewrite vtx_img_graph vtx_mk_graph; apply/imfsetP.
    by exists (low_lexibasis xV1); rewrite ?inE.
Qed.

End StructCons.

Lemma target_correctness: giso computed_graph target_graph.
Proof.
exists id; apply: sub_gisof => //.
- apply/fsubsetP=> x; rewrite in_fsetE /= vtx_mk_graph in_fsetE /= RatG.vtx_mem_list; exact: mem_foo.
- exact: edge_target.
- exact/(giso_connected (lexi_giso _))/lexi_connected.
- by move=> x xVc; rewrite low_succE //; apply/fsetP=> y; rewrite inE.
- exact: cgraph_neq0.
Qed.

Lemma witness : exists x, x \in vertices (lexi_graph target_Po).
Proof.
case/graph0Pn : cgraph_neq0=> x.
rewrite vtx_mk_graph inE RatG.vtx_mem_list=> xVc.
by exists (low_lexibasis xVc); rewrite vtx_mk_graph inE.
Qed.

Lemma correctness : giso computed_graph (lexi_graph target_Po).
Proof.
apply/(giso_trans target_correctness)/(giso_sym (xchoose witness)); last exact:lexi_giso.
Qed.

End RelGraph.

Section VtxGraph.


Let n := RatP.n.
Let m := RatP.m.
Context (base : m.-tuple lrel[rat]_n).
Context (fmask_max : {fset m.-choose n} -> m.-choose n).
Hypothesis fmask_max_mem : forall S, fmask_max S \in S.

Definition pert_Po := perturbation base.
Definition pert_mask_graph := lexi_graph pert_Po.

Definition mat_lhs : 'M_(m,n) := \matrix_(i < m) (base`_i).1^T.
Definition mat_rhs : 'cV_m := \col_(i < m) (base`_i).2.

Definition Pbase : base_t := [fset x in val base].

Definition active_ineq_mask x : bitseq := [seq x \in [hp e]%PH | e <- base].

Definition active_ineq_chooses x :=
  [fset l : m.-choose n | mask_sub l (active_ineq_mask x)].

Definition lhs_mask (l : m.-choose n):= rowsub (fmask_nth l) mat_lhs.
Definition rhs_mask (l : m.-choose n):= rowsub (fmask_nth l) mat_rhs. 

Definition active_ineq_lexibasis x :=
    [fset l in active_ineq_chooses x | lhs_mask l \in unitmx]. 

Lemma active_ineq_maskE x l : l \in active_ineq_lexibasis x ->
  (rowsub (fmask_nth l) mat_lhs) *m x = (rowsub (fmask_nth l) mat_rhs) .
Proof.
(* case/imfsetP=> /= mas; rewrite !inE -andbA => /and3P [_ ].
rewrite /active_ineq_mask /= => /mask_subP + + E.
rewrite {}E size_fmask => h_sub h_inv; apply/row_matrixP=> i.
rewrite row_mul !row_rowsub.
set j := fmask_nth _ _.
move: (h_sub j); rewrite fmask_nth_mask -fmask_nthP /=.
Admitted. *)
Admitted.

Definition active_ineq_span x := <<mask (active_ineq_mask x) base>>%VS.
Definition active_ineq_maxbasis x := fmask_max (active_ineq_lexibasis x).

End VtxGraph.





(* matrix X of size n * (1+m) such that
 * all (fun e => e.1^T * X = e.2) base  *)


(* Definition all_sat (x : 'M[rat]_(n,m.+1)) :=
  all (fun l => sat_ineq l x) base_p.

Definition sat_mask (mas : bitseq) (x : 'M[rat]_(n, m.+1)) :=
  all (fun l => sat_ineq l x) (mask mas base_p).

Definition eq_mask (mas : bitseq) (x : 'M[rat]_(n, m.+1)) :=
  all (fun l => sat_eq l x) (mask mas base_p). *)

(* Definition lexi_preaxiom (b : (bitseq * 'M[rat]_(n,m.+1))%type) :=
  [&& all_sat b.2, card_bitseq b.1 == n,
    size b.1 == m & eq_mask b.1 b.2]. *)

(* Record lexi_prebasis := Lexi {
  prebase :> (bitseq * 'M[rat]_(n,m.+1))%type;
  preaxiom : lexi_preaxiom prebase
}. *)

(* Record extract_mask := Lexi {
  emask :> m.-tuple bool;
  eaxiom : (card_bitseq emask == n)
}.

Canonical emask_subType := [subType for emask].
Definition emask_eqMixin := [eqMixin of extract_mask by <:].
Canonical emask_eqType := EqType _ emask_eqMixin.
Definition emask_choiceMixin := [choiceMixin of extract_mask by <:].
Canonical emask_choiceType := ChoiceType _ emask_choiceMixin.
Check [finType of m.-tuple bool].
Definition emask_finMixin := [finm] *)


(* Lemma lexi_preaxiomP (L : extract_masks) :
  lexi_preaxiom L.
Proof. exact: preaxiom. Qed.

Lemma lexi_all_sat (L : extract_masks) :
  all_sat (lexi_point L).
Proof. by case/and4P: (lexi_preaxiomP L). Qed. *)


(*
Lemma lexi_eq_mask (L: lexi_prebasis) :
  eq_mask (lexi_mask L) (lexi_point L).
Proof. by case/and4P: (lexi_preaxiomP L). Qed.

Lemma lexi_sat_maskP (L: lexi_prebasis) x:
  all_sat x -> sat_mask (lexi_mask L) x.
Proof. move=> ?; exact: all_mask. Qed. *)








(* Lemma lexi_solP (L: lexi_prebasis):
  (lexi_matrix L) *m (lexi_point L) = (lexi_aff L).
Proof. exact/lexi_mtx_affP/lexi_eq_mask. Qed.

Lemma lexi_mtx_satP (L: lexi_prebasis) x:
  sat_mask (lexi_mask L) x ->
  forall i, ((row i (lexi_matrix L)) *m x) >=lex (row i (lexi_aff L)).
Proof.
move/allP=> /= sat_x i; rewrite !rowK -!map_mask.
move: (ltn_ord i). rewrite -[in X in (_ < X)%nat -> _](lexi_card L)=> size_m.
rewrite !(nth_map 0) ?size_mask ?lexi_size ?base_size //.
by apply/sat_x/mem_nth; rewrite size_mask ?lexi_size ?base_size.
Qed.


(* ------------------------------------------------------------------- *)

Definition is_basis (L : lexi_prebasis) : bool :=
  (lexi_matrix L) \in unitmx.

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

Lemma lexi_pointP (L : lexi_basis) M:
  eq_mask (lexi_mask L) M -> M = (lexi_point L).
Proof.
move : (lexi_solP L) => + /lexi_mtx_affP; move=> <-.
apply: row_full_inj; rewrite row_full_unit; exact: lexi_basisP.
Qed.

End LexiBasis.

Section LexPivot.

Context {n m: nat} (base_p : seq ('rV[rat]_n * 'rV[rat]_m.+1)).
(* Hypothesis base_size: size base_p = m. *)

Context (v : 'M[rat]_(n,m.+1)) (d : 'cV[rat]_n).


Definition direction_mask :=
  [seq ((x.1 *m d) 0 0) < 0 | x <- base_p].

Definition direction_unfeasible :=
  seq.has id direction_mask.

Definition gap_d (x : ('rV[rat]_n * 'rV[rat]_m.+1)) :=
  ((x.1 *m d) 0 0)^-1 *: (x.2 - (x.1 *m v)).


Definition gaps :=
  [seq gap_d x| x <- (mask direction_mask base_p)].

Definition min_gap := lex_min_seq gaps.

Definition along_dir := v + d *m min_gap.

Hypothesis dirN : direction_unfeasible.
Hypothesis sat_v : all_sat base_p v.


Lemma gapsN0 : gaps != [::].
Proof.
rewrite /gaps -size_eq0 size_map size_mask ?size_map //; move: dirN.
rewrite /direction_unfeasible has_count; exact: lt0n_neq0.
Qed.


Lemma min_gap_ge0: min_gap >=lex 0.
Proof.
rewrite /min_gap.
move/has_nthP: (lex_min_seq_eq gapsN0)=> /= /(_ 0) [i + /eqP ->].
rewrite /gaps -filter_mask size_map size_filter => i_ord.
set s := [seq _ | _ <- _ & _ ].
move: (@mem_nth _ 0 s i).
have ilts: (i < size s)%nat by rewrite size_map size_filter.
case/(_ ilts)/mapP => /= x; rewrite mem_filter=> /andP [x_dir x_base] ->.
apply: lex_scalar_le0.
- by rewrite invr_le0 (ltW x_dir).
- rewrite lex_subr_le0; move/allP: sat_v; exact.
Qed.

Lemma min_gapP b: b \in base_p -> ((b.1 *m d) 0 0) < 0 ->
  min_gap <=lex (gap_d b).
Proof.
move=> base_b b_dir; apply/lex_min_seq_ler/map_f.
by rewrite -filter_mask mem_filter base_b b_dir.
Qed.


Lemma along_dirP: all_sat base_p along_dir.
Proof.
apply/allP=> b b_base_p.
rewrite /sat_ineq /along_dir mulmxDr mulmxA.
have ->: b.1 *m d *m min_gap = ((b.1 *m d) 0 0) *: min_gap.
- by apply/matrixP=> i j; rewrite !mxE (ord1_eq0 i) /= big_ord1 !mxE.
case: (ltrgt0P ((b.1 *m d) 0 0)).
- move=> h.
  move/(lex0_nnscalar (ltW h)): (min_gap_ge0) => dir_ge0.
  move/allP: sat_v=> /(_ b b_base_p) => sat_b.
  by move: (lex_add sat_b dir_ge0); rewrite addr0.
- move=> h; move: (min_gapP b_base_p h).
  rewrite (lex_negscalar _ _ h) -(lex_add2l (b.1 *m v)).
  rewrite scalerA mulrV ?unitf_lt0 //.
  by rewrite scale1r addrCA addrN addr0.
- move=> ->; rewrite scale0r addr0.
  move/allP: sat_v; exact.
Qed.

End LexPivot.

Section MaxLexBase.

Context {n' : nat} (n := n'.+1) (base : base_t[rat,n]).
Context (x : 'cV[rat]_n).
Hypothesis x_poly : x \in 'P(base)%PH.

Definition active_ineq_mask :=
  [seq (e.1^T *m x) == (const_mx e.2) | e : lrel <- (enum_fset base)].

Definition span_gen  {K : fieldType} {vT : vectType K} (s : seq vT) :=
  (foldr
  (fun v acc => let: (base, rema) := acc in
    if v \in <<rema>>%VS then (base, behead rema) else (v::base, behead rema))
  ([::], behead s) s).1.

Definition active1 :=
  [seq e.1 | e : lrel <- (mask active_ineq_mask (enum_fset base))].

Definition maxLexi_mask :=
  [seq e.1 \in span_gen active1 | e : lrel <- (enum_fset base)].

Lemma span_genP {K : fieldType} {vT : vectType K} (s : seq vT) (v : vT):
  v \in s -> v \notin (span_gen s) ->
  v \in << drop (index v s).+1 s>>%VS.
Proof.
Admitted.

End MaxLexBase.
*)
