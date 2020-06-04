(* --------------------------------------------------------------------
 * Copyright (c) - 2017--2020 - Xavier Allamigeon <xavier.allamigeon at inria.fr>
 * Copyright (c) - 2017--2020 - Ricardo D. Katz <katz@cifasis-conicet.gov.ar>
 * Copyright (c) - 2019--2020 - Pierre-Yves Strub <pierre-yves@strub.nu>
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
Require Import Recdef.
From mathcomp Require Import all_ssreflect ssrnum ssralg zmodp matrix mxalgebra vector finmap.
Require Import extra_misc inner_product extra_matrix xorder vector_order row_submx xvector.
Require Import hpolyhedron polyhedron barycenter poly_base.

Import Order.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope poly_scope.
Import GRing.Theory Num.Theory.

(* Goal :

On suppose qu'on est à la base admissible I, et on considère i \in I.

Pour tout j \notin I, on note
- c_ij := A_j * (col i A_I^{-1}) <- c_{ij} := '[j.1, d] pour j \in base `\` I, où
d est tel que affine << I \` i >> = [line d & _] et '[i.1, d] = 1
- r_j := A_j x^I - b_j (qui ne dépend pas de i)

Proposition
Soit I une base admissible, i \in I, et j \notin I. Alors J = I - i + j est une base admissible ssi les conditions suivantes sont satisfaites :
* c_ij != 0
* r_j > 0 ==> j \in arg max_(k notin I | c_ik < 0) (r_k / c_ik).

*)

Section PBasis.
Context {R : realFieldType} {n : nat} {base : base_t[R,n]}.
Context (P : {poly base}).
Hypothesis Pprop0 : P `>` [poly0].
Hypothesis n_proper0 : (n > 0)%N. (*Necessity ?*)

Implicit Type (I : {fsubset base}).

Lemma span_polyEq (I J : base_t) :
  (<<I>> = <<J>>)%VS -> 'P^=(base; I) = 'P^=(base; J).
Proof.
by rewrite !polyEq_affine => ->.
Qed.

Lemma basis_polyEq (I J : base_t) :
  basis_of <<I>>%VS J -> 'P^=(base; I) = 'P^=(base; J).
Proof.
by move/span_basis/span_polyEq.
Qed.

Definition is_pbasis I :=
   [&& (#|` I | == n)%N, (dim (affine <<I>>%VS) == 1)%N & (affine <<I>>%VS `<=` P)].

(*Definition is_pbasis I :=
  [&& (#|` I | == n)%N, (\dim <<I>> == n)%N & ([poly0] `<` 'P^=(base; I) `<=` P)].*)

Lemma card_pbasis I :
  is_pbasis I -> #|` I | = n.
Proof.
by case/and3P => /eqP.
Qed.

(*Definition point_of_pbasis I := ppick (affine <<I>>%VS).
Lemma point_of_pbasisP I :
  is_pbasis I -> affine <<I>>%VS = [pt (point_of_pbasis I)].*)


Lemma pbasis_proper0 I :
  is_pbasis I -> affine <<I>> `>` [poly0]. (*affine <<I>>%VS `>` .*)
Proof.
by case/and3P => _ /eqP dimI _; rewrite dimN0 dimI.
Qed.

Lemma pbasis_feasible I :
  is_pbasis I -> affine <<I>> `<=` P.
Proof.
by case/and3P.
Qed.

Lemma dim_affine_pbasis I :
  is_pbasis I -> (dim (affine <<I>>) = 1)%N.
Proof.
by case/and3P => _ /eqP.
Qed.

Lemma pbasis_active I :
  is_pbasis I -> 'P^=(base; I) = affine <<I>>.
Proof.
move => pbasisI; rewrite polyEq_affine.
apply/meet_idPr/(le_trans (pbasis_feasible _)) => //.
exact: poly_base_subset.
Qed.

(*Lemma span_pbasis I :
  is_pbasis I -> (<< I >> = << {eq 'P^=(base; I)%:poly_base} >>)%VS.
Proof.
Admitted.*)

Lemma pbasis_vertex I :
  is_pbasis I -> exists2 x, x \in vertex_set P & affine <<I>> = [pt x].
Proof.
move => pbasis_I.
case/eqP/dim1P: (dim_affine_pbasis pbasis_I) => x ptPbaseI.
move : (pbasis_feasible pbasis_I).
rewrite ptPbaseI; move => ptx_subset_P; exists x => //.
rewrite in_vertex_setP -ptPbaseI face_setE.
- by rewrite ptPbaseI.
- by rewrite -pbasis_active // pvalP.
Qed.

Lemma vertexP (x : 'cV_n) :
  x \in vertex_set P ->
        exists Q : {poly base}, [/\ [pt x] = Q, dim Q = 1%N & (Q `<=` P :> 'poly[R]_n)].
Proof.
case/imfsetP => Q /=; rewrite inE => /andP [].
case/face_setP => {}Q ? _ /eqP ? ->.
by exists Q; split; rewrite -?dim1_pt_ppick.
Qed.

Lemma vertex_pbasis x :
  x \in vertex_set P -> exists2 I, is_pbasis I & [pt x] = affine <<I>>%VS.
Proof.
case/vertexP => Q [-> dimQ_eq1 Q_sub_P].
have Q_prop0: Q `>` [poly0] by rewrite dimN0 dimQ_eq1.
have dim_eqQ: (\dim <<{eq Q}>> = n)%N.
- apply/anti_leq/andP; split; rewrite ?dim_span_active //.
  move: dimQ_eq1; rewrite dimN0_eq // => /succn_inj/eqP.
  by rewrite subn_eq0.
case: (ebasisP0 {eq Q}) => I I_sub I_basis.
have I_sub_base: (I `<=` base)%fset. (* TODO: missing canonical in fsubset *)
- by apply/(fsubset_trans I_sub)/fsubset_subP.
have I_pbasis : is_pbasis (I%:fsub).
- apply/and3P; split => /=.
  + by rewrite (card_basis I_basis) dim_eqQ.
  + by rewrite (span_basis I_basis) -hullN0_eq // -dim_hull dimQ_eq1.
  + by rewrite (span_basis I_basis) -hullN0_eq //
  (dim1_pt_ppick dimQ_eq1) hull_pt -dim1_pt_ppick.
exists (I%:fsub) => //.
rewrite -pbasis_active // (span_polyEq (span_basis I_basis)).
by rewrite [Q in LHS]repr_active //=.
Qed.

Definition adj_basis I I' := #|` (I `&` I') |%fset = n.-1.
Definition adj_vertex x x' := (x != x') && ([segm x & x'] \in face_set P).

Lemma adj_vertexL x x' : adj_vertex x x' -> x \in vertex_set P.
Proof.
case/andP => ? /vertex_setS; rewrite vertex_set_segm.
move/fsubsetP => H.
by apply: (H x); rewrite !inE eq_refl /=.
Qed.

Lemma adj_vertexR x x' : adj_vertex x x' -> x' \in vertex_set P.
Proof.
case/andP => ? /vertex_setS; rewrite vertex_set_segm.
move/fsubsetP => H.
by apply: (H x'); rewrite !inE eq_refl orbT.
Qed.


Lemma adj_vertex_prebasis x x':
  adj_vertex x x' -> exists J : {fsubset base},
    [/\ [segm x & x'] = 'P^=(base; J)%:poly_base, (\dim <<J>>)%N = n.-1 & free J].
Proof.
rewrite /adj_vertex => /andP [x_neq_x'].
case/face_setP => Q Q_sub_P Q_eq.
have Q_prop0: Q `>` [poly0] by rewrite -Q_eq segm_prop0.
case: (ebasisP0 {eq Q}) => J J_sub J_basis.
have J_sub' : (J `<=` base)%fset
  by apply/(fsubset_trans J_sub)/fsubset_subP.
exists J%:fsub; split.
- by rewrite [Q]repr_active //= (basis_polyEq J_basis).
- have dimQ2: (dim Q) = 2%N by rewrite -Q_eq dim_segm x_neq_x'.
move: (span_basis J_basis) => ->.
rewrite (dimN0_eq Q_prop0) in dimQ2. move/eq_add_S: dimQ2 => dimQeq.
rewrite -subn1 -dimQeq subKn => //.
by apply ltnW; rewrite -subn_gt0 dimQeq.
- by move/basis_free: J_basis.
Qed.

Definition is_pbasis_of (x : 'cV_n) (I : {fsubset base}) :=
  is_pbasis I /\ [pt x] = affine <<I>>%VS.

Lemma is_pbasis_of_pbasis (x: 'cV_n) (I : {fsubset base}) :
is_pbasis_of x I -> is_pbasis I.
Proof.
by case.
Qed.

Lemma is_pbasis_of_eq x I : is_pbasis_of x I -> [pt x] = affine <<I>>%VS.
Proof.
by case.
Qed.

Lemma vertex_pbasis_of I x :
  x \in vertex_set P ->
        let Qx : {poly base} := insubd [poly0]%:poly_base [pt x] in
        basis_of <<{eq Qx}>>%VS I -> is_pbasis_of x I.
Proof.
move => x_vtx.
case/vertexP: (x_vtx) => Q [Q_eq dim_Q Q_sub].
rewrite Q_eq valKd /= => basis_eqQ_I.
have Q_prop0: [ poly0 ] `<` Q by rewrite -Q_eq pt_proper0.
have x_eq : [pt x] = affine <<I>>.
+ by rewrite (span_basis basis_eqQ_I) -hullN0_eq // -Q_eq hull_pt.
split => //; apply/and3P; split; rewrite -?x_eq ?dim_pt ?Q_eq //.
rewrite (card_basis basis_eqQ_I).
rewrite dimN0_eq in dim_Q => //.
move/succn_inj/eqP: dim_Q; rewrite subn_eq0 => n_leq_dim.
by apply/eqP/anti_leq/andP; split => //; rewrite dim_span_active.
Qed.

Lemma free_card (K : fieldType) (vT : vectType K) (X : {fset vT}) :
  free X -> (\dim <<X>> = #|` X |)%N.
Admitted.

Lemma adj_vertex_basis x x' :
  adj_vertex x x' -> exists I, exists I',
      [/\ is_pbasis_of x I, is_pbasis_of x' I' & adj_basis I I'].
Proof.
move=> adj_x_x'.
case: (adj_vertex_prebasis adj_x_x') => J [segm_J dim_J free_J].
have x_vtx := (adj_vertexL adj_x_x').
have x_vtx' := (adj_vertexR adj_x_x').
have: [pt x] \in face_set P /\ [pt x'] \in face_set P
  by rewrite -!in_vertex_setP.
case => /face_setP [Qx Qxsub Qxpt] /face_setP [Qx' Qx'sub Qx'pt].
set S := ('P^=(base; J)) %:poly_base.
have [eq_sub_eq_x eq_sub_eq_x'] : ({eq S} `<=` {eq Qx})%fset /\ ({eq S} `<=` {eq Qx'})%fset.
- rewrite !activeS // -segm_J -1?Qxpt -1?Qx'pt pt_subset.
  + by rewrite in_segmr.
  + by rewrite in_segml.
have J_sub_eqS: (J `<=` {eq S})%fset by rewrite -activeP le_refl.
have {}eq_sub_eq_x : (J `<=` {eq Qx})%fset.
- by apply: (fsubset_trans J_sub_eqS).
have {}eq_sub_eq_x' : (J `<=` {eq Qx'})%fset.
- by apply: (fsubset_trans J_sub_eqS).
rewrite {J_sub_eqS}.
case: (ebasisP eq_sub_eq_x free_J) => I [J_sub_I I_sub_eq_x I_basis].
case: (ebasisP eq_sub_eq_x' free_J) => I' [J_sub_I' I'_sub_eq_x' I'_basis].
have I_sub_base: (I `<=` base)%fset.
- by apply/(fsubset_trans I_sub_eq_x)/fsubset_subP.
  (* TODO: valP should work instead of
   * fsubset_subP *)
have I'_sub_base: (I' `<=` base)%fset.
- by apply/(fsubset_trans I'_sub_eq_x')/fsubset_subP.
  (* TODO: valP should work instead of
   * fsubset_subP *)
exists I%:fsub; exists I'%:fsub.
have is_pbasis_of_x_I : is_pbasis_of x I%:fsub.
- apply/vertex_pbasis_of => //; by rewrite Qxpt valKd.
have is_pbasis_of_x'_I' : is_pbasis_of x' I'%:fsub.
- apply/vertex_pbasis_of => //; by rewrite Qx'pt valKd.
split => //.
have card_J: (#|` J | = n.-1)%N by rewrite -free_card.
rewrite /adj_basis /=.
suff ->: (I `&` I')%fset = J by [].
apply/eqP; rewrite eq_sym eqEfcard card_J; apply/andP; split.
- by apply/fsubsetIP.
- have: Qx `>` [ poly0 ] /\ Qx' `>` [ poly0 ]
  by split; rewrite -?Qxpt -?Qx'pt pt_proper0.
  case=> proper_Qx proper_Qx'.
  have: #|` I| = n /\ #|`I'| = n.
  split.
  + rewrite (card_basis I_basis); move: (dimN0_eq proper_Qx).
    rewrite -Qxpt dim_pt; move/eq_add_S => H.
    by rewrite -[RHS](subnKC (dim_span_active proper_Qx)) -H addn0.
  + rewrite (card_basis I'_basis); move: (dimN0_eq proper_Qx').
    rewrite -Qx'pt dim_pt; move/eq_add_S => H.
    by rewrite -[RHS](subnKC (dim_span_active proper_Qx')) -H addn0.
  case=> card_I card_I'.
  have: ~(I =i I').
  + move/eq_span => eqspans.
    have: [pt x] = [pt x']
      by rewrite (is_pbasis_of_eq is_pbasis_of_x_I)
      (is_pbasis_of_eq is_pbasis_of_x'_I') /= eqspans.
    case/predD1P: (adj_x_x') => x_neq_x' ? eq_pt.
    by apply x_neq_x'; rewrite -(ppick_pt x) -(ppick_pt x') eq_pt.
  move/fsetP/eqP; apply/contraR; rewrite -ltnNge => least_cardI.
  have cardII': (#|` (I `&` I')%fset | = n)%N.
  + apply/anti_leq/andP; split.
    * rewrite -[Y in (_ <= Y)%N]card_I; apply: fsubset_leq_card;
      exact: fsubsetIl.
    * by rewrite -[Y in (Y <= _)%N](prednK n_proper0).
  rewrite eqEfsubset; apply/andP; split.
  + by apply/fsetIidPl/eqP; rewrite eqEfcard fsubsetIl card_I cardII' /=.
  + by apply/fsetIidPr/eqP; rewrite eqEfcard fsubsetIr card_I' cardII' /=.  
Qed.
  

(* Proof sketch:
 * start from x x' satisfying adj_vertex x x'
 * extract J from adj_vertex_prebasis
 * Then we have x \in 'P^=(base; J), so that
 * J \subset {eq 'P^=(base; J)} \subset {eq [pt x]%:poly_base} (see activeS)
 * apply ebasisP to complete J into a basis I of <<{eq [pt x]%:poly_base}>> containing J
 * since dim <<{eq [pt x]%:poly_base}>> = n, then I is J + one element,
 * apply the same proof to x', which provided I' such that #|` I `&` I'| = n.-1
 *)


Lemma foo' x (I : {fsubset base}) :
  x \in P -> [pt x] = affine <<I>>%VS -> #|` I| = n -> is_pbasis I.
Proof.
move => x_in_P pt_eq cardI.
apply/and3P; split; rewrite -?pt_eq.
- by apply/eqP.
- by rewrite dim_pt.
- by rewrite pt_subset.
Qed.

(*move => H; case: (adj_vertex_prebasis H) => J; case => PbaseJ cardJ.
case/andP: H => x_neq_x' /face_setP [] Q Q_sub_P Qeq.
have x_vtx: x \in vertex_set Q.
- by rewrite -Qeq vertex_set_segm in_fset2 eq_refl.
rewrite in_vertex_setP in x_vtx.
case/face_setP: x_vtx => Qx Qx_sub_Q ptx_eq.
have x'_vtx: x' \in vertex_set Q.
- by rewrite -Qeq vertex_set_segm in_fset2 eq_refl orbT.
rewrite in_vertex_setP in x'_vtx.
case/face_setP: x'_vtx => Qx' Qx'_sub_Q ptx'_eq.*)

(*move/vertex_set_face/fsetP; rewrite vertex_set_segm /eq_mem.
Search _ Imfset.imfset.*)


(*Lemma dim_pbasisD1 I i :
  is_pbasis I -> (i \in (I : {fset _}))
  -> dim (affine << (I `\ i)%fset >>%VS) = 2%N.
Proof.
move => I_pbasis i_in_I /=.
Admitted.*)

Lemma dim_pbasisD1' I i :
  is_pbasis I -> i \in (I : {fset _}) ->
    exists d, (affine << (I `\ i)%fset >> == [line d & (ppick 'P^=(base; I))]) && ('[i.1, d] == 1).
Admitted.

Definition dir I i (H : is_pbasis I) (H' : i \in (I : {fset _})) :=
  xchoose (dim_pbasisD1' H H').

Definition c I i (H : is_pbasis I) (H' : i \in (I : {fset _})) (j : lrel[R]_n) :=
  '[j.1, dir H H'].

Definition r I (j : lrel[R]_n) :=
  '[j.1, ppick (affine << I >>%VS)] - j.2.

End PBasis.
