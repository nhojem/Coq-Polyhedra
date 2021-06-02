(* --------------------------------------------------------------------
 * Copyright (c) - 2017--2021 - Xavier Allamigeon <xavier.allamigeon at inria.fr>
 * Copyright (c) - 2017--2021 - Ricardo D. Katz <katz@cifasis-conicet.gov.ar>
 * Copyright (c) - 2019--2021 - Pierre-Yves Strub <pierre-yves@strub.nu>
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect all_algebra finmap.
Require Import extra_misc inner_product vector_order extra_matrix row_submx.
Require Import simplex barycenter lrel.

Import Order.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GRing.Theory Num.Theory.

(* -------------------------------------------------------------------- *)
Reserved Notation "P .`c" (at level 2, format "P .`c").
Reserved Notation "P .`A" (at level 2, format "P .`A").
Reserved Notation "P .`b" (at level 2, format "P .`b").
Reserved Notation "''hpoly[' R ]_ n" (at level 8, format "''hpoly[' R ]_ n").
Reserved Notation "''hpoly_' n" (at level 8, format "''hpoly_' n").

(* -------------------------------------------------------------------- *)
Module HPolyhedron.

Section Def.

Variable (R : realFieldType) (n : nat).

Record hpoly := HPoly {
  nb_ineq : nat ;
  _ : 'M[R]_(nb_ineq,n) ;
  _ : 'cV[R]_nb_ineq
}.

Definition mem_hpoly P : {pred 'cV[R]_n} :=
  let: HPoly _ A b := P in
  [pred x : 'cV_n | (A *m x) >=m b].
Coercion mem_hpoly : hpoly >-> pred_sort.

End Def.

Notation "''hpoly[' R ]_ n" := (hpoly R n).
Notation "''hpoly_' n" := (hpoly _ n).

Section Choice.

Variable R : realFieldType.
Variable n : nat.

Definition matrix_from_hpoly (P : 'hpoly[R]_n) :=
  let: HPoly _ A b := P in
    Tagged (fun m => 'M[R]_(m,n) * 'cV[R]_m)%type (A, b).

Definition hpoly_from_matrix (M : {m : nat & 'M[R]_(m,n) * 'cV[R]_m}%type) :=
  let: (A, b) := tagged M in
    HPoly A b.

Lemma matrix_from_hpolyK :
  cancel matrix_from_hpoly hpoly_from_matrix.
Proof.
by move => [m A b]; rewrite /matrix_from_hpoly /hpoly_from_matrix.
Qed.

Definition hpoly_eqMixin := CanEqMixin matrix_from_hpolyK.
Canonical hpoly_eqType := Eval hnf in EqType 'hpoly[R]_n hpoly_eqMixin.
Definition hpoly_choiceMixin := CanChoiceMixin matrix_from_hpolyK.
Canonical hpoly_choiceType := Eval hnf in ChoiceType 'hpoly[R]_n hpoly_choiceMixin.

End Choice.

Section PolyPred.

Context {R : realFieldType} {n : nat}.

Implicit Type (P : 'hpoly[R]_n).

Definition hpoly_c (P : 'hpoly[R]_n) : nat
  := let: HPoly c A b := P in c.

Definition hpoly_A (P : 'hpoly[R]_n) :'M_(hpoly_c P, _)
  := let: HPoly c A b := P in A.

Definition hpoly_b (P : 'hpoly[R]_n) :'cV_(hpoly_c P)
  := let: HPoly c A b := P in b.

Notation "P .`c" := (hpoly_c P).
Notation "P .`A" := (hpoly_A P).
Notation "P .`b" := (hpoly_b P).

Lemma in_hpolyE (P : 'hpoly[R]_n) x : (x \in P) = (P.`A *m x) >=m (P.`b).
Proof. by case: P. Qed.

Definition mk_hs (b : lrel[R]_n) : 'hpoly[R]_n := HPoly (b.1)^T (b.2)%:M.

Lemma in_hs b x : x \in (mk_hs b ) = ('[b.1,x] >= b.2).
Proof.
rewrite inE vdotC -vdot_def.
by apply/forallP/idP => [ /(_ 0) | H i]; rewrite ?[i]ord1_eq0 !mxE /= !mulr1n.
Qed.

Definition poly0 := mk_hs [<0,1>].

Lemma in_poly0 : poly0 =i pred0.
Proof.
by move => x; rewrite in_hs vdot0l inE ler10.
Qed.

Definition polyT : 'hpoly[R]_n := @HPoly _ _ 0 (const_mx 0) 0.

Lemma in_polyT : polyT =i predT.
Proof.
by move => x; rewrite !inE mul0mx lev_refl.
Qed.

Definition polyI P Q :=
  let: HPoly _ A b := P in
  let: HPoly _ A' b' := Q in
    HPoly (col_mx A A') (col_mx b b').

Lemma in_polyI P Q : (polyI P Q) =i [predI P & Q].
Proof.
move => x.
case: P => mP AP bP; case: Q => mQ AQ bQ.
by rewrite !inE mul_col_mx col_mx_lev.
Qed.

Definition bounded P c :=
  let: HPoly _ A b := P in
    Simplex.bounded A b c.

Definition opt_value P c :=
  let: HPoly _ A b := P in
    Simplex.opt_value A b c.

Definition poly_subset P Q :=
  let: HPoly _ A b := P in
  let: HPoly _ A' b' := Q in
    (~~ Simplex.feasible A b) ||
      [forall i, (Simplex.bounded A b (row i A')^T) && (Simplex.opt_value A b (row i A')^T >= b' i 0)].

(*Lemma poly_subsetP {P Q : 'hpoly[R]_n} :
  reflect {subset P <= Q} (poly_subset P Q).
Proof. (* RK *)
case: P => m A b; case: Q => m' A' b'.
apply: (iffP idP) => [/orP poly_subset_P_Q | subset_P_Q].
- case: poly_subset_P_Q => [empty_P | /forallP hs_incl x x_in_P].
  + move => x x_in_P.
    move: empty_P; apply/contraR => _.
    by apply/Simplex.feasibleP; exists x.
  + apply/forallP => i.
    move/andP: (hs_incl i) => [/Simplex.boundedP [_ opt_is_opt] ?].
    apply: (@le_trans _ _ (Simplex.opt_value A b (row i A')^T) _ _); first by done.
    by rewrite -row_vdot; apply: opt_is_opt.
- apply/orP.
  case: (boolP (Simplex.feasible A b)) => [feasible_P | _]; last by left.
  right.
  apply/forallP => i.
  suff bounded_P_row_i_A': Simplex.bounded A b (row i A')^T.
    apply/andP; split; first exact: bounded_P_row_i_A'.
    move/Simplex.boundedP: bounded_P_row_i_A' => [[x [/subset_P_Q  x_in_Q <-]] _].
    rewrite row_vdot.
    exact: ((forallP x_in_Q) i).
  apply/(Simplex.boundedP_lower_bound _ feasible_P).
  exists (b' i 0).
  move => x /subset_P_Q x_in_Q.
  rewrite row_vdot.
  exact: ((forallP x_in_Q) i).
Qed.*)

Lemma poly_subsetPn {P Q : 'hpoly[R]_n} :
  reflect (exists2 x, x \in P & x \notin Q) (~~ (poly_subset P Q)).
Proof. (* RK *)
case: P => m A b; case: Q => m' A' b'.
apply: (iffP idP) => [| [x] x_in_P not_in_Q]; last first.
- move: not_in_Q; apply/contra; rewrite /poly_subset.
  move/orP; case => [empty_P | /forallP hs_incl].
  + move: empty_P; apply/contraR => _.
    by apply/Simplex.feasibleP; exists x.
  + apply/forallP => i.
    move/andP: (hs_incl i) => [/Simplex.boundedP [_ opt_is_opt] ?].
    apply: (@le_trans _ _ (Simplex.opt_value A b (row i A')^T) _ _); first by done.
    by rewrite -row_vdot; apply: opt_is_opt.
- rewrite negb_or negbK negb_forall.
  move/andP => [feasible_P /existsP [i /nandP unbounded_or]].
  have unbounded_suff:
    ~~ Simplex.bounded A b (row i A')^T -> exists2 x : 'cV_n, (x \in HPoly A b) & (x \notin HPoly A' b').
  + rewrite -(Simplex.unbounded_is_not_bounded _ feasible_P) => /Simplex.unboundedP unbounded_P_row_i_A'.
    move: (unbounded_P_row_i_A' (b' i 0)) => [x [x_in_P ineq]].
    exists x; try by done.
    move: ineq; apply: contraL => x_in_Q.
    rewrite -leNgt row_vdot.
    exact: ((forallP x_in_Q) i).
  case: unbounded_or; first exact: unbounded_suff.
  case: (boolP (Simplex.bounded A b (row i A')^T)) => [? | ? _]; last by apply: unbounded_suff.
  rewrite -ltNge => ineq.
  exists (Simplex.opt_point A b (row i A')^T); first exact: Simplex.opt_point_is_feasible.
  move: ineq; apply: contraL => opt_point_in_Q.
  rewrite -leNgt /Simplex.opt_value row_vdot.
  exact: ((forallP opt_point_in_Q) i).
Qed.

Lemma poly_subsetP {P Q : 'hpoly[R]_n} :
  reflect {subset P <= Q} (poly_subset P Q).
Proof.
apply/(iffP idP) => [P_sub_Q x x_in_P | P_sub_Q].
- move: P_sub_Q; apply: contraTT => x_notin_Q.
  by apply/poly_subsetPn; exists x.
- by apply: contraT; move/poly_subsetPn => [x] /P_sub_Q ->.
Qed.

Lemma boundedP (P : 'hpoly[R]_n) c :
  reflect (exists2 x, (x \in P) & poly_subset P (mk_hs [<c, '[c,x]>])) (bounded P c).
Proof. (* RK *)
case: P => m A b.
apply/(equivP (Simplex.boundedP A b c) _);
  split => [[[x [? opt_value_eq]] opt_value_is_opt] | [x ? /poly_subsetP incl_hs]].
- exists x; first by done.
  apply/poly_subsetP => y y_in_P.
  rewrite in_hs opt_value_eq.
  by apply: opt_value_is_opt.
- have opt_value_eq: '[ c, x] = Simplex.opt_value A b c.
    apply: Simplex.opt_value_is_optimal; first by done.
    by move => y /incl_hs; rewrite in_hs.
  split.
  + by exists x.
  + move => y /incl_hs.
    by rewrite in_hs -opt_value_eq.
Qed.

Lemma boundedPn P c :
  ~~ (poly_subset P poly0) ->
    reflect (forall K, ~~ (poly_subset P (mk_hs [<c, K>]))) (~~ bounded P c).
Proof. (* RK *)
case: P => m A b non_empty_P.
have feasible_P: Simplex.feasible A b
  by move/poly_subsetPn: non_empty_P => [x ? _];
  apply/Simplex.feasibleP; exists x.
rewrite /bounded (Simplex.bounded_is_not_unbounded c feasible_P) negbK.
apply/(equivP (Simplex.unboundedP A b c) _);
  split => [unbounded_cond_point K | unbounded_cond_hs K].
- apply/poly_subsetPn.
  move: (unbounded_cond_point K) => [x [? val_x_sineq]].
  exists x; first by done.
  by rewrite in_hs -ltNge.
- move/poly_subsetPn: (unbounded_cond_hs K) => [x ? x_not_in_hs].
  exists x; split; first by done.
  by rewrite in_hs -ltNge in x_not_in_hs.
Qed.

Definition pointed P :=
  ~~ (poly_subset P poly0) ==>
  let: HPoly _ A _ := P in Simplex.pointed A.

Lemma pointedPn P :
  reflect (exists x, exists2 d, (d != 0) & (forall μ, x + μ *: d \in P)) (~~ pointed P).
Proof. (* RK *)
case: P => [m A b].
rewrite /pointed; apply/(iffP idP).
- rewrite negb_imply => /andP [/poly_subsetPn [x x_in _]].
  move/Simplex.pointedPn =>
  [d [d_neq0 /Simplex.feasible_dirP d_feas_dir /Simplex.feasible_dirP md_feas_dir]].
  exists x; exists d => //.
  move => μ; case: (lerP 0 μ) => [?|?].
  + apply/d_feas_dir => //; exists x => //.
  + rewrite -[d]opprK scalerN -scaleNr.
    apply/md_feas_dir => //.
    by rewrite oppr_ge0 ltW.
- move => [x [d d_neq0 sub]].
  have x_in : x \in HPoly A b by move/(_ 0): sub; rewrite scale0r addr0.
  have -> /=: ~~ poly_subset (HPoly A b) poly0 by apply/poly_subsetPn; exists x => //; rewrite in_poly0.
  apply/Simplex.pointedPn.
  by exists d; split => //; apply/(Simplex.feasible_dirP _ x_in) => [μ _];
     rewrite ?scalerN -?scaleNr; apply/sub.
Qed.

Lemma convexP2 (P : 'hpoly[R]_n) (v w : 'cV[R]_n) α :
  v \in P -> w \in P -> 0 <= α <= 1 -> (1-α) *: v + α *: w \in P.
Proof.
case: P => m A b.
rewrite !inE => vP wP.
case/andP => [gt0_a lt1_a]; rewrite mulmxDr -!scalemxAr.
rewrite -[b]scale1r -{1}[1](subrK α) scalerDl.
by rewrite lev_add // lev_wpscalar // subr_ge0.
Qed.

Definition poly_equiv P Q := (poly_subset P Q) && (poly_subset Q P).

Lemma poly_equivP {P Q : 'hpoly[R]_n} : reflect (P =i Q) (poly_equiv P Q).
Proof.
apply/(iffP andP) => [[/poly_subsetP P_le_Q /poly_subsetP Q_le_P] x | P_eq_Q ].
- apply/idP/idP; [exact: P_le_Q | exact: Q_le_P].
- by split; apply/poly_subsetP => x; rewrite P_eq_Q.
Qed.

Lemma poly_equiv_refl : reflexive poly_equiv.
Proof.
by move => P; apply/poly_equivP.
Qed.

Lemma poly_equiv_sym : symmetric poly_equiv.
Proof.
by move => P Q; apply: (sameP poly_equivP);
   apply: (iffP poly_equivP) => [H x | H x]; rewrite H.
Qed.

Lemma poly_equiv_trans : transitive poly_equiv.
Proof.
move => P' P P'' /poly_equivP P_eq_P' /poly_equivP P'_eq_P''.
by apply/poly_equivP => x; rewrite P_eq_P'.
Qed.

(* -------------------------------------------------------------------- *)
Section Farkas.
Variable (base : base_t[R,n]).

Let P := \big[polyI/polyT]_(b : base) (mk_hs (val b)).

Notation m := #|`base|.

Let A := \matrix_(i < m) ((fnth i).1)^T.
Let b :=    \col_(i < m) (fnth i).2.

Lemma fnth_baseE i : @fnth _ base i = [< col i A^T, b i 0 >].
Proof.
apply/eqP/lrel_eqP => /=; split.
* by apply/colP=> k; rewrite !mxE. * by rewrite mxE.
Qed.

Lemma combinemE w :
  combine (vect_to_fsfun w) = [< A^T *m w, '[b, w] >].
Proof.
rewrite (combinewE (finsupp_vect_to_fsfun _)).
pose h (i : 'I_m) := [`fnthP i]%fset.
rewrite (reindex h) /=; last first.
+ by apply/onW_bij/(Bijective (@frankK _ _) (@fnthK _ _)).
apply: (can_inj (@col_to_lrelK _ _)) => /=.
rewrite lrel_to_colM raddf_sum /= mulmx_sum_col.
apply: eq_bigr=> i _; rewrite linearZ /=.
rewrite /vect_to_fsfun fsfun_ffun insubT /=; first by apply: fnthP.
move=> hin; rewrite [hin](bool_irrelevance _ (fnthP i)) frankK.
rewrite tr_row_mx col_col_mx; apply/colP=> j.
rewrite /lrel_to_col !fnth_baseE /=.
rewrite (_ : const_mx _ = col i b^T) //.
by apply/colP=> k; rewrite !mxE.
Qed.

Lemma memP : P =i HPoly A b.
Proof.
move=> x; have [hI h0] := (fun P1 P2 => in_polyI P1 P2 x, in_polyT x).
rewrite {hI h0}(big_morph (fun P => x \in P) hI h0).
rewrite !inE big_andE; apply/forall_inP/forallP => /= h.
+ move=> i; move/(_ [`fnthP i]%fset isT): h.
  rewrite inE /= !fnth_baseE /= -tr_row trmxK.
  by rewrite -row_mul row_cV -lev_scalar_mx.
+ move=> e _; rewrite inE /=; move/(_ (frank e)): h.
  have: fnth (frank e) = fsval [`fnthP (frank e)]%fset by [].
  rewrite {1}fnth_baseE fnthK => <- /=; rewrite lev_scalar_mx.
  by rewrite tr_col trmxK -row_mul row_cV.
Qed.

Lemma farkas (e : lrel) :
     ~~ (poly_subset P poly0)
  -> (poly_subset P (mk_hs e))
  -> exists2 w : {conic lrel ~> R},
         (finsupp w `<=` base)%fset
       & (combine w).1 = e.1 /\ (combine w).2 >= e.2.
Proof.
move=> nz_P /poly_subsetP le_Pe; case: (Simplex.simplexP A b e.1).
+ move=> d /(intro_existsT (Simplex.infeasibleP _ _)) /negP[].
  apply/Simplex.feasibleP; case/poly_subsetPn: nz_P => [x x_in_P _].
  by exists x; rewrite inE memP in x_in_P |- *.
+ move=> p /(intro_existsT (Simplex.unboundedP_cert _ _ _)).
  case/Simplex.unboundedP/(_ e.2) => [x [x_in_PAb ineq]].
  have /le_Pe: x \in P by rewrite memP inE.
  by rewrite in_hs => /(lt_le_trans ineq); rewrite ltxx.
+ case=> [x w] [x_feas w_feas csc]; move: w_feas.
  rewrite inE /= => /andP[/eqP w_feas1 w_pos].
  exists (mkConicFun (conic_vect_to_fsfun w_pos)).
  + by apply: finsupp_vect_to_fsfun.
  + rewrite combinemE /=; split => //.
    by rewrite -csc -in_hs le_Pe //= memP inE.
Qed.
End Farkas.
End PolyPred.

Section Lift.

Variable (R : realFieldType) (n k : nat).

Definition lift_poly (P : 'hpoly[R]_n) : 'hpoly[R]_(n+k) :=
  let: HPoly _ A b := P in
  HPoly (row_mx A 0) b.

Lemma lift_polyP (P : 'hpoly[R]_n) x :
  (x \in lift_poly P) = (usubmx x \in P).
Proof.
rewrite /lift_poly; case: P => m A b.
by rewrite !inE -{1}[x]vsubmxK mul_row_col mul0mx addr0.
Qed.

End Lift.

Module Import Exports.
Canonical hpoly_eqType.
Canonical hpoly_choiceType.
Notation "''hpoly[' R ]_ n" := (@hpoly R n).
Notation "''hpoly_' n" := ('hpoly[_]_n).
Notation "P .`c" := (hpoly_c P).
Notation "P .`A" := (hpoly_A P).
Notation "P .`b" := (hpoly_b P).
End Exports.
End HPolyhedron.

Export HPolyhedron.Exports.
Coercion mem_hpoly := HPolyhedron.mem_hpoly.
