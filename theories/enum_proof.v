From mathcomp Require Import all_ssreflect all_algebra finmap.
Require Import extra_misc inner_product extra_matrix vector_order.
Require Import lrel.
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
  @row_mx _ _ 1 m (const_mx b) (- delta_mx 0 k).


Definition perturbation_seq : seq plrel :=
  map
  (fun x: lrel[R]_n * 'I_m => (x.1.1^T , create_perturbation x.1.2 x.2))
  (zip base (enum  'I_m)).

Lemma size_pert_: size perturbation_seq == m.
Proof. by rewrite size_map size_zip size_tuple size_enum_ord minnn. Qed.

Definition perturbation := Tuple size_pert_.

Lemma size_pert : size perturbation = m.
Proof. apply/eqP/size_pert_. Qed.

Lemma nth_pert (i : 'I_m) : perturbation`_ i = ((base`_ i).1^T , (row_mx ((const_mx (base`_ i).2) : 'M_(1,1)) (- delta_mx 0 i))).
Proof.
rewrite (nth_map (lrel0, i)) /= ?size_zip ?size_enum_ord ?size_tuple ?minnn //.
rewrite !nth_zip ?size_enum_ord ?size_tuple //=; congr pair.
by rewrite nth_ord_enum.
Qed.

End Perturbation.

Section LexiBasis.

Context (R : realFieldType) (n m : nat).
Context (base : m.-tuple (plrel n m R)).

Definition A_base := unzip1 base.
Definition b_base := unzip2 base.

Record lexi_prebasis := Lexi {
  s :> m.-choose n;
  _ : basis_of fullv (mask s A_base);
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

Lemma lexi_vbasis (L : lexi_prebasis) : basis_of fullv (mask L A_base).
Proof. by case: L => ? /=. Qed.

Definition mask_matrix (L : m.-choose n) : 'M_n :=
  \matrix_(i < n) ((mask L A_base)`_i).

Definition mask_aff (L :  m.-choose n) : 'M_(n, m.+1) :=
  \matrix_(i < n) (mask L b_base)`_i.

Lemma mask_matrixP (L : m.-choose n) (i : 'I_n):
  row i (mask_matrix L) = (mask L A_base)`_i.
Proof. by rewrite rowK. Qed.

Lemma mask_affP (L : m.-choose n) (i : 'I_n):
  row i (mask_aff L) = (mask L b_base)`_i.
Proof. by rewrite rowK. Qed.

Lemma mtx_vbasisE (L : m.-choose n) :
  reflect (basis_of fullv (mask L A_base)) (mask_matrix L \in unitmx).
Proof.
(*apply/(iffP idP).
- rewrite -row_full_unit basisEdim size_mask ?size_tuple //.
  rewrite card_fmask dimvf /Vector.dim /= mul1n leqnn andbT.
  case/row_fullP => B Bdef; apply/subvP=> x _.
  Search _ row_full. *)
Admitted.

Lemma lexi_matrix_inv (L : lexi_prebasis) : (mask_matrix L) \in unitmx.
Proof. exact/mtx_vbasisE/lexi_vbasis. Qed.

Definition lexi_point (L : lexi_prebasis) : 'M_(n, m.+1) :=
  (invmx (mask_matrix L)) *m (mask_aff L).

(* ---------------------------------------------------------------------------- *)

Definition all_sat (x : 'M[R]_(n,m.+1)) :=
  all (fun l => sat_ineq l x) base.

Definition sat_mask (mas : bitseq) (x : 'M[R]_(n, m.+1)) :=
  all (fun l => sat_ineq l x) (mask mas base).

Definition eq_mask (mas : bitseq) (x : 'M[R]_(n, m.+1)) :=
  all (fun l => sat_eq l x) (mask mas base).

Lemma prelexi_mask_point (L : m.-choose n) x :
  eq_mask L x ->
  (mask_matrix L) *m x = (mask_aff L).
Proof.
move=> /allP /= eqx.
apply/row_matrixP => i.
rewrite row_mul !rowK -!map_mask.
rewrite !(nth_map 0) ?size_mask ?size_tuple ?card_fmask //=.
by apply/eqP/eqx/mem_nth; rewrite ?size_mask ?size_tuple ?card_fmask.
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
rewrite /lexi_point /sat_eq mulmxA.
have ->: ((mask L base)`_i).1 = row (Ordinal i_ord) (mask_matrix L) by
  rewrite mask_matrixP -map_mask (nth_map 0) ?size_mask ?size_tuple ?card_fmask.
rewrite -row_mul mulmxV ?lexi_matrix_inv // -row_mul mul1mx.
by rewrite mask_affP -map_mask (nth_map 0) ?size_mask ?size_tuple ?card_fmask.
Qed.


Definition lexi_graph :=
  mk_graph [fset L | L : lexi_basis]
    (fun L1 L2 => ##| maskI L1 L2 | == (n-1)%N).

(* TODO: map sur des graphes
   + lemme d'isomorphisme entre ces graphes *)


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

Hypothesis g_struct : RatA.struct_consistent n target_Po g.
Hypothesis g_vtx : RatA.vertex_consistent target_Po g.

Definition computed_graph := mk_graph [fset x | x in RatG.vertex_list g] (RatG.mem_edge g).
Hypothesis cgraph_neq0 : computed_graph != (graph0 _).
(* TODO : Mandatory hypothesis ?*)
Hypothesis cgraph_sym : {in (RatG.vertex_list g)&, symmetric (RatG.mem_edge g)}.

Definition low_point k := if RatG.label g k is Some l then l else 0.

Section LowPointIng.

Context (k : bitseq).
Hypothesis k_mem : RatG.mem_vertex g k.

Lemma mem_low_size: size k == m.
Proof.
move/RatG.vertex_allP: g_struct=> H.
case/RatG.vtx_memE: k_mem=> e /H/and4P [].
by rewrite size_pert.
Qed.

Definition kt := Tuple mem_low_size.

Lemma mem_low_card: ##|kt| == n.
Proof.
move/RatG.vertex_allP: g_struct=> H.
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
  (mask_matrix target_Po km) *m (low_point km) = (mask_aff target_Po km).
Proof. exact/prelexi_mask_point/mem_low_mask. Qed.

Definition col_mask :=
  [seq (mask_matrix target_Po km) *m (col j (low_point km)) != 0 |
  j <- behead (enum 'I_m.+1)].

Lemma col'_mul {R : realFieldType} {p q r : nat} (M : 'M[R]_(p,q)) (N : 'M[R]_(q,r)) j: col' j (M *m N) = M *m (col' j N).
Proof.
by rewrite !col'Esub mulmx_colsub.
Qed.

Lemma col_maskP : (mask_matrix target_Po km) *m colsub ((lift 0) \o fmask_nth km) (low_point km) = 1%:M.
Proof.
rewrite mulmx_colsub low_mtx_affP colsub_comp.
rewrite !mxE -map_mask (nth_map 0) ?size_mask ?card_fmask ?size_fmask ?size_pert //.
rewrite -map_mask (nth_map (lrel0, (fmask_nth km i))) ?size_mask ?card_fmask ?size_fmask ?size_zip ?size_enum_ord ?size_tuple ?minnn //=.
rewrite /create_perturbation.
Search _ row_mx.



Lemma col_maskP j : (mask_matrix target_Po km) *m (col (fmask_nth km j) (col' 0 (low_point km))) = delta_mx j 0.
Proof.
rewrite -col_mul.
Search _ (col').

Lemma col_mask_card: ##| col_mask | == n.
Proof.
rewrite /col_mask.
Admitted.


Definition fcol_mask := CMask col_mask_card.

Program Definition extr_low_point :=
  colsub (fmask_nth fcol_mask) (col' 0 (low_point k)).
Next Obligation. by rewrite card_ord. Defined.

Lemma extr_low_pointE : (mask_matrix target_Po km) *m extr_low_point = 1%:M.
Proof.
Admitted.

Lemma extr_low_inv : (mask_matrix target_Po km) \in unitmx.
Proof. by case/mulmx1_unit: extr_low_pointE. Qed.

Lemma low_vbasis: basis_of fullv (mask km (A_base target_Po)).
Proof. exact/mtx_vbasisE/extr_low_inv. Qed.

Definition low_prebasis := Lexi low_vbasis.

Lemma low_lexipoint : lexi_point low_prebasis = low_point km.
Proof.
Admitted.

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
move/RatG.vertex_allP: g_struct => vtx_cond; rewrite RatG.edge_mem_list => y_nei_x.
have: RatG.neighbour_list g x != [::] by move: y_nei_x; case: (RatG.neighbour_list g x).
move/RatG.neighbour_list_mem => /[dup] xg /RatG.vtx_memE [e] /vtx_cond.
case/and4P=> _ _ /RatG.neighbour_allP.
by move/(_ xg _ y_nei_x).
Qed.

Lemma edge_target : {in vertices computed_graph &, forall x y,
  edges computed_graph x y -> edges target_graph x y}.
Proof.
move=> x y; rewrite vtx_mk_graph !inE /= !RatG.vtx_mem_list=> xVc yVc.
rewrite edge_mk_graph ?inE ?RatG.vtx_mem_list //.
move=> or_edge; apply/edge_img_graph.
exists (low_lexibasis xVc); exists (low_lexibasis yVc); split=> //=.
rewrite edge_mk_graph ?inE //=; apply/orP.
case/orP: or_edge; [left|right]; exact:low_edge.
Qed.

Lemma regular_computed : regular computed_graph n.
Proof.
move=> x; rewrite vtx_mk_graph inE RatG.vtx_mem_list => xVc.
case/RatG.vtx_memE : (xVc) => e x_find_e.
move/RatG.vertex_allP : g_struct => /(_ x e x_find_e).
case/and4P => _ _ _; rewrite RatG.nb_neighbours_list //.
move/eqP/Some_inj => <-; rewrite succC_mk_graph ?inE ?RatG.vtx_mem_list //=.
- move/perm_size: (RatG.neighbour_listE g x) => ->.
  rewrite card_imfset //= !size_filter /=; apply/permP.
  apply/(perm_trans (enum_imfset _ _))=> //=.
  by rewrite map_id undup_id ?RatG.uniq_vtx_list ?perm_refl.
- move=> v w /imfsetP /= [v' v'_vtx ->] /imfsetP [/= w' w'_vtx ->].
  by rewrite cgraph_sym.
Qed.

Lemma low_succE : {in vertices computed_graph, forall x,
  successors computed_graph x = successors target_graph x}.
Proof.
move=> x xV1; apply/eqP; rewrite eqEfcard; apply/andP; split.
- apply/fsubsetP=> y; rewrite !in_succE=> /[dup] /edge_vtxr yV1.
  exact:(edge_target).
- rewrite (regular_computed xV1) (giso_regular (n:=n) (lexi_giso _)) //.
  + exact/lexi_regular.
  + rewrite vtx_mk_graph inE RatG.vtx_mem_list in xV1.
    rewrite vtx_img_graph vtx_mk_graph; apply/imfsetP.
    by exists (low_lexibasis xV1); rewrite ?inE.
Qed.

End StructCons.

Lemma foo: giso computed_graph target_graph.
Proof.
exists id; apply: bar => //.
- apply/fsubsetP=> x; rewrite in_fsetE /= vtx_mk_graph in_fsetE /= RatG.vtx_mem_list; exact: mem_foo.
- exact: edge_target. 
- exact/(giso_connected (lexi_giso _))/lexi_connected.
- by move=> x xVc; rewrite low_succE //; apply/fsetP=> y; rewrite inE.
Qed.

Lemma witness : exists x, x \in vertices (lexi_graph target_Po).
Proof.
case/graph0Pn : cgraph_neq0=> x.
rewrite vtx_mk_graph inE RatG.vtx_mem_list=> xVc.
by exists (low_lexibasis xVc); rewrite vtx_mk_graph inE.
Qed.

Lemma correctness : giso computed_graph (lexi_graph target_Po).
Proof.
apply/(giso_trans foo)/(giso_sym (xchoose witness)); last exact:lexi_giso.
Qed.


End RelGraph.




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
