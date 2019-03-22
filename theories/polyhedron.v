(*************************************************************************)
(* Coq-Polyhedra: formalizing convex polyhedra in Coq/SSReflect          *)
(*                                                                       *)
(* (c) Copyright 2017, Xavier Allamigeon (xavier.allamigeon at inria.fr) *)
(*                     Ricardo D. Katz (katz at cifasis-conicet.gov.ar)  *)
(*                     Vasileios Charisopoulos (vharisop at gmail.com)   *)
(* All rights reserved.                                                  *)
(* You may distribute this file under the terms of the CeCILL-B license  *)
(*************************************************************************)

From mathcomp Require Import all_ssreflect ssralg ssrnum zmodp matrix mxalgebra vector perm finmap (*fingroup*).
Require Import extra_misc inner_product vector_order extra_matrix row_submx simplex polypred hpolyhedron.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope poly_scope.
Import GRing.Theory Num.Theory.

Section PredSort.

Variable (R : realFieldType) (n : nat).

Definition poly_sort := PolyPred.sort [polyPredType of 'poly[R]_n].
Canonical poly_sort_eqType := Eval hnf in [eqType of poly_sort].
Canonical poly_sort_choiceType := Eval hnf in [choiceType of poly_sort].
Canonical poly_sort_predType := Eval hnf in [predType of poly_sort].
Canonical poly_sort_choicePredType := Eval hnf in [choicePredType of poly_sort].
Canonical poly_sort_polyPredType := Eval hnf in [polyPredType of poly_sort].
Identity Coercion poly_sort_to_polypred: poly_sort >-> PolyPred.sort.

End PredSort.

Section PolyBase.

Variable (R : realFieldType) (n : nat) (base : 'hpoly[R]_n).

Definition has_base (P : poly_sort R n) :=
  [exists I, P == '['P^=(base; I)]].

Inductive poly_base := PolyBase { pval :> poly_sort R n ; _ : has_base pval}.
Canonical poly_base_subType := [subType for pval].
Definition poly_base_eqMixin := Eval hnf in [eqMixin of poly_base by <:].
Canonical poly_base_eqType := Eval hnf in EqType poly_base poly_base_eqMixin.
Definition poly_base_choiceMixin := Eval hnf in [choiceMixin of poly_base by <:].
Canonical poly_base_choiceType := Eval hnf in ChoiceType poly_base poly_base_choiceMixin.
Coercion poly_base_to_poly P := (pval P : 'poly[R]_n).

Lemma poly_baseP (P : poly_base) : has_base P.
Proof.
exact: valP.
Qed.

Lemma has_baseP {P} : reflect (exists I, P = '['P^=(base; I)]) (has_base P).
Proof.
exact: exists_eqP.
Qed.

Lemma polyEq_base I :
  has_base '['P^=(base; I)].
Proof.
by apply/has_baseP; exists I.
Qed.

Definition set_of_poly_base (P : poly_base) : {set 'I_(#ineq base)} :=
  xchoose (existsP (poly_baseP P)).

Definition set_of_poly_base_pinv (I : {set 'I_(#ineq base)})  : option poly_base :=
  let P := PolyBase (polyEq_base I) in
  if I == set_of_poly_base P then Some P else None.

Lemma set_of_poly_baseK :
  pcancel set_of_poly_base set_of_poly_base_pinv.
Proof.
move => P.
rewrite /set_of_poly_base_pinv; last first.
case: ifP; last first.
- move/negbT/negP.
  suff <-: P = PolyBase (polyEq_base (xchoose (existsP (poly_baseP P)))) by done.
  apply/val_inj/eqP => /=; exact: (xchooseP (existsP (poly_baseP P))).
- set P' := PolyBase (polyEq_base (xchoose (existsP (poly_baseP P)))).
  move/eqP => set_eq_set'.
  suff ->: (P = P' :> poly_base) by done.
  move/eqP: (xchooseP (existsP (poly_baseP P))).
  rewrite /set_of_poly_base in set_eq_set'; rewrite set_eq_set'.
  move/eqP: (xchooseP (existsP (poly_baseP P'))) => <-.
  exact: val_inj.
Qed.

Definition poly_base_countMixin := PcanCountMixin set_of_poly_baseK.
Canonical poly_base_countType := Eval hnf in CountType poly_base poly_base_countMixin.
Definition poly_base_finMixin := PcanFinMixin set_of_poly_baseK.
Canonical poly_base_finType := Eval hnf in FinType poly_base poly_base_finMixin.

End PolyBase.

Notation "'{poly'  base '}'" := (poly_base base).
Notation "[ P 'has' '\base' base ]" := (has_base base P).

Section Test.

Variable (R : realFieldType) (n : nat) (base : 'hpoly[R]_n).

Variables (P Q : {poly base}) (Q' : 'poly[R]_n) (x : 'cV[R]_n).

Set Printing Coercions.

Check (x \in P).
Check (P : 'poly[R]_n).

Goal P `<=` Q' -> forall x, x \in P -> x \in Q'.
move/poly_subsetP => H z z_in_P.
by move/H: z_in_P.
Qed.

Unset Printing Coercions.

End Test.

Section HasBase.

Variable (R : realFieldType) (n : nat).

Implicit Type (base : 'hpoly[R]_n) (P : 'poly[R]_n).

Lemma has_base_subset base P :
  [ P has \base base ] -> P `<=` '[base].
Proof.
move/has_baseP => [I ->]; rewrite quotE; exact: hpolyEq_antimono0.
Qed.

Lemma self_base (base : 'hpoly[R]_n) :
  ['[base] has \base base].
Proof.
apply/has_baseP; exists set0; symmetry; apply/quotP; exact: hpolyEq0.
Qed.

Lemma repr_base (P : 'poly[R]_n) :
  [P has \base (\repr P)].
Proof.
case/hpolyP: P => m A b; exact: self_base.
Qed.

End HasBase.

Section Face.

Variable (R : realFieldType) (n : nat) (base : 'hpoly[R]_n).

Implicit Type (P : {poly base}).

Definition face_set P : {set {poly base}} :=
  [set Q : {poly base} | (`[poly0] `<` Q `<=` P)].

Lemma face_set_self P : (P `>` `[poly0]) -> P \in (face_set P).
Proof.
move => ?; rewrite inE; apply/andP; split; [done | exact: poly_subset_refl].
Qed.

(* BUG below, we should be able to write :> (poly_sort R n) instead *)
Lemma poly0_face_set P : ((P : poly_sort _ _) = (`[poly0] : poly_sort _ _)) -> face_set P = set0.
Proof.
move => P_eq0; apply/setP => Q; rewrite !inE P_eq0.
apply: negbTE; apply/negP => /andP [Q_gt0 Q_le0].
by move: (poly_proper_subset Q_gt0 Q_le0); rewrite poly_properxx.
Qed.

End Face.

Module FaceBase.
Section FaceBase.



Variable (R : realFieldType) (n : nat) (base : 'hpoly[R]_n).

Let P := '[base].

Definition face_set : {fset 'poly[R]_n} :=
  [fset '['P^=(base; I)] | I : {set 'I_(#ineq base)}
                               & ('['P^=(base; I)] `>` `[poly0]) ]%fset.



Lemma argmin_in_face_set c :
  bounded P c -> argmin P c \in face_set.
Admitted.

Lemma faceP {Q} :
  reflect (exists2 c, Q = argmin P c & bounded P c) (Q \in face_set).
Admitted.

Lemma face_proper0 Q : Q \in face_set -> Q `>` `[poly0].
Proof.
by move/imfsetP => /= [I]; rewrite inE => ? ->.
Qed.

Lemma face_polyEq Q : Q \in face_set -> exists I, Q = '['P^=(base; I)] /\ Q `>` `[poly0].
Proof.
by move/imfsetP => /= [I]; rewrite inE => ? ->; exists I.
Qed.

Lemma polyEq_face I : ('['P^=(base; I)] `>` `[poly0]) -> '['P^=(base; I)] \in face_set.
Proof.
by move => non_empty; apply/imfsetP; exists I; rewrite ?inE //=.
Qed.

End FaceBase.
End FaceBase.

Section Face.

Context {R : realFieldType} {n : nat}.

Implicit Type (P Q : 'poly[R]_n).

Definition face_set P : {fset 'poly[R]_n} := FaceBase.face_set (\repr P).

Lemma poly0_face_set : face_set '[poly0] = fset0.
Proof.
by apply: FaceBase.poly0_face_set; rewrite reprK.
Qed.

Lemma face_set_self P : (P `>` `[poly0]) -> P \in face_set P.
Proof.
rewrite /face_set; case/hpolyP: P => m A b; exact: FaceBase.face_set_self.
Qed.

Lemma argmin_in_face_set P c :
  bounded P c -> argmin P c \in face_set P.
Proof.
rewrite /face_set; case/hpolyP: P => m A b; exact: FaceBase.argmin_in_face_set.
Qed.

Lemma faceP {P Q} :
  reflect (exists2 c, Q = argmin P c & bounded P c) (Q \in face_set P).
rewrite /face_set; case/hpolyP: P => m A b; exact: FaceBase.faceP.
Qed.

Lemma face_set_base base :
  face_set '[base] = [fset '['P^=(base; I)] | I : {set 'I_(#ineq base)} & ('['P^=(base; I)] `>` `[poly0]) ]%fset.
Proof.
rewrite -/(FaceBase.face_set base).
apply/fsetP => Q; apply: (sameP faceP); exact: FaceBase.faceP.
Qed.

Lemma face_proper0 P Q : Q \in face_set P -> Q `>` `[poly0].
Proof.
rewrite /face_set; case/hpolyP: P => m A b; exact: FaceBase.face_proper0.
Qed.

Lemma face_polyEq base Q :
  Q \in face_set '[base] -> exists I, Q = '['P^=(base; I)] /\ Q `>` `[poly0].
Proof.
rewrite face_set_base; exact: FaceBase.face_polyEq.
Qed.

Lemma polyEq_face base I : ('['P^=(base; I)] `>` `[poly0]) -> '['P^=(base; I)] \in (face_set '[base]).
Proof.
rewrite face_set_base; exact: FaceBase.polyEq_face.
Qed.

Lemma polyI_face P Q Q' :
  Q \in face_set P -> Q' \in face_set P ->  ((Q `&` Q') `>` `[poly0]) -> (Q `&` Q') \in face_set P.
Proof.
case/hpolyP: P => m A b; move => /face_polyEq [I] [-> _] /face_polyEq [I'] [-> _].
rewrite polyEq_polyI; exact: polyEq_face.
Qed.

Lemma face_subset P Q : Q \in face_set P -> Q `<=` P.
Proof.
case/hpolyP: P => m A b; move => /face_polyEq [I] [-> _].
rewrite quotE; exact: hpolyEq_antimono0.
Qed.

Lemma face_set_subset P Q :
  Q \in face_set P -> (face_set Q `<=` face_set P)%fset.
Proof.
case/hpolyP: P => m A b.
move => /face_polyEq [I] [-> _].
apply/fsubsetP => Q' /face_polyEq [I'] [->].
move: (hpolyEq_of_hpolyEq I') => [K] /quotP ->.
exact: polyEq_face.
Qed.

Lemma face_set_of_face (P Q : 'poly[R]_n) :
  Q \in face_set P -> face_set Q = [fset Q' in face_set P | (Q' `<=` Q)%PH]%fset.
Proof.
move => Q_face.
apply/eqP; rewrite eqEfsubset; apply/andP; split; apply/fsubsetP.
- move => Q' Q'_face.
  rewrite in_fsetE inE; apply/andP; split; last exact: face_subset.
  by move: Q' Q'_face; apply/fsubsetP; exact: face_set_subset.
- move => Q'; rewrite in_fsetE inE => /= /andP [Q'_face].
  move/faceP : Q'_face => [c [-> c_bounded_on_P]] argminPc_sub_Q.
  have c_bounded_on_Q : bounded Q c
    by apply: (bounded_mono1 c_bounded_on_P); exact: (face_subset Q_face).
  suff ->: argmin P c = argmin Q c by exact: argmin_in_face_set.
  rewrite [RHS]argmin_polyI.
  suff <-: opt_value c_bounded_on_P = opt_value c_bounded_on_Q.
  + apply/quot_equivP/andP; split.
    * apply/poly_subsetIP; split; first by done.
      rewrite argmin_polyI; exact: poly_subsetIr.
    * rewrite argmin_polyI; apply: polySI; exact: face_subset.
  + apply/eqP; rewrite eqr_le; apply/andP; split.
    * apply: opt_value_antimono1; exact: (face_subset Q_face).
    * have /proper0P [x x_in]: (argmin P c `>` `[poly0])
        by rewrite -bounded_argminN0. (* bounded_argminN0 is not easy to use *)
      move/(poly_subsetP argminPc_sub_Q) : (x_in).
      suff <-: '[c,x] = opt_value c_bounded_on_P.
      - move/(poly_subsetP (opt_value_lower_bound c_bounded_on_Q)).
        by rewrite inE.
      - move/(poly_subsetP (argmin_opt_value c_bounded_on_P)): x_in.
        by rewrite inE => /eqP.
Qed.

End Face.

Section Base.

Context {R : realFieldType} {n : nat}.

Implicit Type (P Q : 'poly[R]_n) (base : 'hpoly[R]_n).

Definition has_base (P : 'poly[R]_n) (base : 'hpoly[R]_n) :=
  [exists I , P == '['P^=(base; I)]].

Notation "[ P 'has' '\base' base ]" := (has_base P base).


Lemma has_base_subset (P : 'poly[R]_n) (base : 'hpoly[R]_n) :
  [ P has \base base ] -> P `<=` '[base].
Proof.
move/has_baseP => [I ->]; rewrite quotE; exact: hpolyEq_antimono0.
Qed.

Lemma polyEq_base (base: 'hpoly[R]_n) I :
  [ '['P^=(base; I)] has \base base ].
Proof.
by apply/has_baseP; exists I.
Qed.

Lemma self_base (P: 'hpoly[R]_n) :
  ['[P] has \base P].
Proof.
apply/has_baseP; exists set0; symmetry; apply/quotP; exact: hpolyEq0.
Qed.

Lemma repr_base (P : 'poly[R]_n) :
  [P has \base (\repr P)].
Proof.
case/hpolyP: P => m A b; exact: self_base.
Qed.


Lemma has_base_face P base :
  [P has \base base] -> (P `>` `[poly0]) -> P \in face_set '[base].
Proof.
move/has_baseP => [I] ->; exact: polyEq_face.
Qed.

Lemma face_has_base P base Q :
  [P has \base base] -> Q \in face_set P -> [Q has \base base].
Proof.
move => P_base.
case: (emptyP P) => [/poly_equivP/quot_equivP ->| P_non_empty].
- by rewrite poly0_face_set in_fset0.
- have: P \in face_set '[base] by exact: has_base_face.
  move => P_face Q_face.
  have /face_polyEq [I [-> _]] : Q \in face_set '[base]
    by move: Q Q_face; apply/fsubsetP; exact: face_set_subset.
  exact: polyEq_base.
Qed.

End Base.

Notation "[ P 'has' '\base' base ]" := (has_base P base).

Section Active.

Context {R : realFieldType} {n : nat}.

Definition active (P : 'poly[R]_n) (base : 'hpoly[R]_n) :=
  \bigcup_(I | P `<=` '['P^=(base; I)]) I.

Notation "'[eq'  P 'on' base ]" := (active P base) : poly_scope.
Notation "'[eq'  P ]" := (active P _) : poly_scope.

Lemma repr_active P base :
  [P has \base base] -> P = '['P^=(base; [eq P])].
Proof.
move => /has_baseP [I0] ->; rewrite -polyEq_big_polyI;
  last by apply/pred0Pn; exists I0; exact: poly_subset_refl.
apply/quot_equivP/andP; split. (* sequence of view is suboptimal *)
- by apply/big_polyIsP => ?.
- by apply/big_poly_inf; exact: poly_subset_refl.
Qed.

Lemma activeP {P base I} : [P has \base base] -> (P `<=` '['P^=(base; I)]) = (I \subset [eq P]).
Proof.
move => P_base; apply/idP/idP; first exact: bigcup_sup.
by rewrite {2}(repr_active P_base); move/hpolyEq_antimono; rewrite quotE.
Qed.

Lemma active_polyEq base (I : {set 'I_(#ineq base)}) : I \subset [eq '['P^=(base; I)] on base].
Proof.
rewrite -activeP; [exact: poly_subset_refl | exact: polyEq_base].
Qed.

Lemma activePn P (m : nat) (A : 'M[R]_(m,n)) (b : 'cV[R]_m) i :
  [P has \base 'P(A,b)] ->
  reflect (exists2 x, x \in P & x \notin (`[hp (row i A)^T & b i 0] : 'poly[R]_n)) (i \notin [eq(P) on 'P(A,b)]).
Proof.
move => P_base; rewrite -sub1set -(activeP P_base).
apply/(iffP poly_subsetPn) => [[x] x_in x_notin | [x] x_in x_notin]; exists x; try by done.
- have x_in_PAb: x \in '['P(A,b)]
    by move: x_in; apply/(poly_subsetP (has_base_subset _)).
  move: x_notin; apply: contraNN; rewrite polyEq1 => x_in_hp.
  by rewrite 2!inE /=; apply/andP; split.
- by move: x_notin; apply: contraNN; rewrite polyEq1 2!inE /= => /andP [_].
Qed.

Lemma subset_on_base P Q base :
  [P has \base base] -> [Q has \base base] ->
    (P `<=` Q) = ([eq Q on base] \subset [eq P on base]).
Proof.
by move => P_base /repr_active {1}->; rewrite activeP.
Qed.

End Active.


(*
Lemma active_inPn i :
  reflect (exists x, x \in P /\ (A *m x) i 0 > b i 0) (i \notin { eq(P) on 'P(A,b) }).
Proof.
apply: (iffP idP); last first.
- move => [x [x_in_P Ai_x_gt_bi]]; apply/negP; move/active_inP/(_ _ x_in_P) => Ai_x_eq_bi.
  by move: Ai_x_gt_bi; rewrite Ai_x_eq_bi ltrr.
- move => i_not_active; set Ai := (row i A)^T.
  case: (lp_stateP (-Ai) P)
  => [P_empty | [x [x_in_P x_opt]] | /(_ (- (b i 0))) [x [x_in_P Ai_x_gt_bi]]].
  + suff: (i \in {eq P on 'P(A,b)}) by move/negP: i_not_active.
    by apply/active_inP => x; rewrite P_empty inE.
  + exists x; split; first by done.
    move: i_not_active; apply: contraR.
    rewrite -lerNgt => Ai_x_le_bi.
    move/has_baseP: P_base => [I P_eq_PAbI].
    apply/active_inP => y y_in_P.
    apply/eqP; rewrite eqr_le; apply/andP; split; last first.
    * by move: y_in_P; rewrite P_eq_PAbI mem_quotP => /hpolyEq_inP [/forallP].
    * move: Ai_x_le_bi; move/(_ _ y_in_P): x_opt.
      rewrite !vdotNl !row_vdot ler_opp2; exact: ler_trans.
  + exists x; split; first by done.
    by rewrite !vdotNl !row_vdot ltr_opp2 in Ai_x_gt_bi.
Qed.*)

(*
Lemma active_osegm v w x i :
  v \in P -> w \in P -> x \in osegm v w ->
    (((A *m x) i 0 > b i 0) = ((A *m v) i 0 > b i 0) || ((A *m w) i 0 > b i 0))
  * (((A *m x) i 0 == b i 0) = ((A *m v) i 0 == b i 0) && ((A *m w) i 0 == b i 0)).
Admitted.
*)


(*

Fact polyIC (P Q : 'poly[R]_n) :
  (P && Q)%PH = (Q && P)%PH.
Proof.
rewrite -[LHS]hpolyK -[RHS]hpolyK; apply/poly_eqP => x.
by rewrite !polyI_inE andbC.
Qed.

Fact polyIA (P Q S : 'poly[R]_n) :
  (P && (Q && S) = (P && Q) && S)%PH.
Proof.
rewrite -[polyI P _]hpolyK -[polyI _ S in RHS]hpolyK; apply/poly_eqP => x.
by rewrite !polyI_inE andbA.
Qed.

Fact polyIid (P : 'poly[R]_n) :
  (P && P)%PH = P.
Proof.
rewrite -[LHS]hpolyK -[P in RHS]hpolyK; apply/poly_eqP => x.
rewrite polyI_inE /=.
by case: (x \in P).
Qed.

Fact poly_subsetIl (P Q : 'poly[R]_n) :
  (P && Q <= P)%PH.
Proof.
apply/poly_subsetP => x.
rewrite polyI_inE.
by move/andP/proj1.
Qed.

Fact poly_subsetIr (P Q : 'poly[R]_n) :
  (P && Q <= Q)%PH.
Proof.
apply/poly_subsetP => x.
rewrite polyI_inE.
by move/andP/proj2.
Qed.

Fact poly_subsetI (P Q S : 'poly[R]_n) :
  (S <= (P && Q))%PH = (S <= P)%PH && (S <= Q)%PH.
Proof.
apply/idP/idP => [S_poly_subset_I | /andP [S_poly_subset_P S_poly_subset_Q]].
- apply/andP; split.
  + by apply/(poly_subset_trans _ (poly_subsetIl P Q)).
  + by apply/(poly_subset_trans _ (poly_subsetIr P Q)).
- apply/poly_subsetP => x x_in_S.
  rewrite polyI_inE.
  apply/andP; split.
  + by apply/(poly_subsetP S_poly_subset_P).
  + by apply/(poly_subsetP S_poly_subset_Q).
Qed.

Fact polyIidPl (P Q : 'poly[R]_n) :
  reflect ((P && Q)%PH = P) (P <= Q)%PH.
Proof.
apply: (iffP idP) => [/poly_subsetP P_subset_Q | polyI_P_Q_eq_P].
- rewrite -[LHS]hpolyK -[RHS]hpolyK; apply/poly_eqP => x.
  rewrite polyI_inE.
  apply: andb_idr.
  exact: (P_subset_Q x).
- apply/poly_subsetP => x.
  rewrite -polyI_P_Q_eq_P.
  exact: ((poly_subsetP (poly_subsetIr P Q)) x).
Qed.

Fact polyIidPr (P Q : 'poly[R]_n) :
  reflect ((P && Q)%PH = Q) (Q <= P)%PH.
Proof.
apply: (iffP idP) => [/poly_subsetP Q_subset_P | polyI_P_Q_eq_Q].
- rewrite -[LHS]hpolyK -[RHS]hpolyK; apply/poly_eqP => x.
  rewrite polyI_inE.
  apply: andb_idl.
  exact: (Q_subset_P x).
- apply/poly_subsetP => x.
  rewrite -polyI_P_Q_eq_Q.
  exact: ((poly_subsetP (poly_subsetIl P Q)) x).
Qed.

*)

(*Fact in_face_affine_hull_rel (P Q : 'poly[R]_n) x :
  Q \in face P ->
    (x \in Q) = ((x \in P) && (x \in affine_hull_of_poly Q)).
Proof.
rewrite inE.
move: (hpoly_base P).
case: (hpoly P) => m A b.
move => P_base /andP [non_empty_Q /andP [Q_base eq_set_incl]].
apply/idP/idP => [x_in_Q | /andP [x_in_P x_in_aff_hull_Q]].
- apply/andP; split.
  + exact: (((subset_on_base P_base Q_base) eq_set_incl) _ x_in_Q).
  + rewrite /affine_hull_of_poly.
    exact: in_poly_imp_in_affine_hull_on_base.
- rewrite (hpoly_of_baseP P_base) mem_quotP inE in x_in_P.
  rewrite (hpoly_of_baseP Q_base) mem_quotP inE.
  apply/andP; split.
  + exact: (proj1 (andP x_in_P)).
  + apply/forallP => i.
    apply/implyP => i_in_eq_Q.
    rewrite (affine_hullP Q_base) (in_affine_hull_on_base _ x non_empty_Q) in x_in_aff_hull_Q.
    move/colP: (eqP x_in_aff_hull_Q) => eq_Q_sat.
    move/eqP: (eq_Q_sat (enum_rank_in i_in_eq_Q i)).
    by rewrite -row_submx_mul 2!row_submx_mxE enum_rankK_in.
Qed.*)

(*Lemma polyI_face_affine_hull (P F : 'poly[R]_n) :
  F \in face P ->
    F = polyI P (affine_hull_of_poly F). (* RK: Proposition 2.3 (iv) of Ziegler's book *)
Proof.
move => F_is_face_of_P.
rewrite -[F]hpolyK -[polyI _ _]hpolyK; apply/poly_eqP => x.
by rewrite polyI_inE (in_face_affine_hull_rel _ F_is_face_of_P) hpolyK.
Qed.*)

Fact polyI_same_base (base : 'hpoly[R]_n) (P Q : 'poly[R]_n) :
  [P has \base base] -> [Q has \base base] ->
    [(P && Q)%PH has \base base].
Proof.
case: base => m A b.
move => /has_baseP [IP P_eq] /has_baseP [IQ Q_eq].
apply/has_baseP; exists (IP :|: IQ).
rewrite (polyI_quotP P_eq Q_eq).
apply/poly_eqP; exact: hpolyEqI_same_base.
Qed.

Fact polyI_eq_same_base (base : 'hpoly[R]_n) (P Q : 'poly[R]_n) :
  ({eq(P) on base} :|: {eq(Q) on base}) \subset {eq((P && Q)%PH) on base}.
Proof.
case: base => m A b.
apply/subsetP => j /setUP [/active_inP cond_in_eq | /active_inP cond_in_eq];
  apply/active_inP => x; rewrite polyI_inE => /andP [x_in_P x_in_Q];
  by apply: cond_in_eq.
Qed.

Fact polyI_concat_base (P Q : 'poly[R]_n) (base_P base_Q : 'hpoly[R]_n) :
  [P has \base base_P] -> [Q has \base base_Q] -> [(P && Q)%PH has \base (hpolyI base_P base_Q)].
Proof.
case: base_P base_Q => [m A b] [m' A' b'].
move => /has_baseP [I P_eq] /has_baseP [I' Q_eq].
rewrite (polyI_quotP P_eq Q_eq) {P_eq Q_eq}; apply/has_baseP.
pose J := ((@lshift m m')@:I) :|: ((@rshift m m')@:I').
exists J; apply/poly_eqP; exact: hpolyEqI_concat_base.
Qed.

Fact polyI_eq_concat_base (P Q : 'poly[R]_n) (m m': nat) (A: 'M[R]_(m,n)) (A' : 'M[R]_(m',n))
  (b: 'cV[R]_m) (b' : 'cV[R]_m') :
  ((@lshift m m') @: {eq P on 'P(A,b)}) :|: ((@rshift m m') @: {eq Q on 'P(A',b')})
                                        \subset {eq (P && Q)%PH on (hpolyI 'P(A,b) 'P(A',b'))}.
Proof.
apply/subsetP => i /setUP
  [/imsetP [i' /active_inP cond_in_eq ->] | /imsetP [i' /active_inP cond_in_eq ->]];
apply/active_inP => x; rewrite mul_col_mx 2?col_mxEu 2?col_mxEd;
move/polyI_inP => [x_in_P x_in_Q]; exact: cond_in_eq.
Qed.



End Intersection.

Arguments polyI_eq_same_base [R n base P Q].
Arguments polyI_eq_concat_base [R n P Q m m' A A' b b'].
Notation "P && Q" := (polyI P Q) : poly_scope.

(*Section Compactness.

Variable R : realFieldType.
Variable n : nat.

Implicit Type P F : 'poly[R]_n.

Definition compact P :=
  (non_empty P) ==> ([forall i, bounded (delta_mx i 0) P && bounded (-(delta_mx i 0)) P]).

Lemma compactP_Linfty P :
  reflect (exists K, forall x, x \in P -> forall i, `|x i 0| <= K) (compact P).
Proof. (* RK *)
apply: (iffP idP) => [/implyP compact_P | [K P_contained_in_box]].
- case: (boolP (non_empty P)) => [non_empty_P| empty_P].
  + set bound_x_i := fun (i : 'I_n) =>
      match (@idP (bounded (delta_mx i 0) P)) with
      | ReflectT bounded_delta_mx_i_P => opt_value bounded_delta_mx_i_P
      | ReflectF _ => 0
      end.
    set bound_minus_x_i := fun (i : 'I_n) =>
      match (@idP (bounded (- delta_mx i 0) P)) with
      | ReflectT bounded_minus_delta_mx_i_P => opt_value bounded_minus_delta_mx_i_P
      | ReflectF _ => 0
      end.
    set K := Num.max (-(min_seq [seq bound_minus_x_i i | i :'I_n] 0)) (-(min_seq [seq bound_x_i i | i :'I_n] 0)).
    exists K.
    move => x x_in_P i.
    rewrite ler_norml.
    apply/andP; split.
    * rewrite oppr_max ler_minl 2!opprK.
      apply/orP; right.
      suff l_bound_x_i: bound_x_i i <= x i 0
        by apply/(ler_trans _ l_bound_x_i)/min_seq_ler/map_f; rewrite mem_enum.
      rewrite /bound_x_i.
      case: {-}_/idP  => [bounded_delta_mx_i_P| /negP not_bounded_delta_mx_i_P].
      - rewrite -vdotl_delta_mx.
        exact: ((proj2 (bounded_opt_value bounded_delta_mx_i_P)) x x_in_P).
      - by rewrite (proj1 (andP (forallP (compact_P non_empty_P) i))) in not_bounded_delta_mx_i_P.
    * rewrite ler_maxr.
      apply/orP; left.
      rewrite ler_oppr.
      suff l_bound_minus_x_i: bound_minus_x_i i <= -x i 0
        by apply/(ler_trans _ l_bound_minus_x_i)/min_seq_ler/map_f; rewrite mem_enum.
      rewrite /bound_minus_x_i.
      case: {-}_/idP  => [bounded_minus_delta_mx_i_P| /negP not_bounded_minus_delta_mx_i_P].
      - rewrite -vdotl_delta_mx -vdotNl.
        exact: ((proj2 (bounded_opt_value bounded_minus_delta_mx_i_P)) x x_in_P).
      - by rewrite (proj2 (andP (forallP (compact_P non_empty_P) i))) in not_bounded_minus_delta_mx_i_P.
  + exists 0.
    move => x x_in_P.
    have non_empty_P: non_empty P
      by apply/non_emptyP; exists x.
    by rewrite non_empty_P in empty_P.
- apply/implyP => non_empty_P.
  apply/forallP => i.
  apply/andP; split; apply/bounded_lower_bound; try by done.
  + exists (-K).
    move => x x_in_P.
    move: (((P_contained_in_box x) x_in_P) i) => x_i_bound.
    rewrite ler_norml in x_i_bound.
    rewrite vdotl_delta_mx.
    exact: (proj1 (andP x_i_bound)).
  + exists (-K).
    move => x x_in_P.
    move: (((P_contained_in_box x) x_in_P) i) => x_i_bound.
    rewrite ler_norml in x_i_bound.
    rewrite vdotNl vdotl_delta_mx ler_oppr opprK.
    exact: (proj2(andP x_i_bound)).
Qed.

Lemma compactP P :
  reflect (non_empty P -> forall c, bounded c P) (compact P). (*RK: statement slightly modified: added the non_empty condition *)
Proof. (* RK *)
apply: (iffP idP) => [/compactP_Linfty [K P_contained_in_box] non_empty_P c | bounded_if_non_empty].
- apply/(bounded_lower_bound c non_empty_P).
  exists (\sum_i (-(`|c i 0| * K))).
  move => x x_in_P.
  rewrite -subr_le0 -sumrB.
  apply: sumr_le0 => i _.
  move/ler_normlP: (((P_contained_in_box x) x_in_P) i) => [? ?].
  rewrite subr_le0 ler_oppl.
  case: (boolP (0 <= c i 0)) => [c_i_geq_0 | c_i_lt_0].
  + rewrite (ger0_norm c_i_geq_0) -mulrN -subr_ge0 -mulrBr.
    apply: mulr_ge0; first exact: c_i_geq_0.
    by rewrite subr_ge0.
  + rewrite -ltrNge in c_i_lt_0.
    rewrite -mulNr -(ltr0_norm c_i_lt_0) -subr_ge0 -mulrBr.
    apply: mulr_ge0; first exact: (normr_ge0 (c i 0)).
    by rewrite subr_ge0.
- case: (boolP (non_empty P)) => [non_empty_P| empty_P].
  + apply/implyP => _; apply/forallP => i.
    by apply/andP; split; exact: (bounded_if_non_empty non_empty_P).
  + apply/implyP => non_empty_P.
    by rewrite non_empty_P in empty_P.
Qed.

End Compactness.*)

Section Compactness.

Variable R : realFieldType.
Variable n : nat.

Implicit Type P F : 'poly[R]_n.

Definition compact P :=
  HPrim.compact (hpoly P).

Lemma compactP_Linfty P :
  reflect (exists K, forall x, x \in P -> forall i, `|x i 0| <= K) (compact P).
Proof. (* RK *)
exact: HPrim.compactP_Linfty.
Qed.

Lemma compactP P :
  reflect (non_empty P -> forall c, bounded c P) (compact P). (*RK: statement slightly modified: added the non_empty condition *)
Proof. (* RK *)
exact: HPrim.compactP.
Qed.

Lemma compact_quotP (hP : 'hpoly[R]_n) :
  compact '[hP] = HPrim.compact hP. (* RK *)
Proof.
apply: (sameP (compactP '[hP])).
rewrite non_empty_quotP.
apply: (iffP idP) => [/HPrim.compactP compact_P non_empty_P c| compact_P].
- by rewrite bounded_quotP; apply: compact_P.
- apply/HPrim.compactP => non_empty_P c.
  by rewrite -bounded_quotP; apply: compact_P.
Qed.

End Compactness.

Section Pointedness.

Variable R : realFieldType.
Variable n : nat.

Implicit Type P : 'poly[R]_n.
(*Variable base : 'hpoly[R]_n.

Hypothesis P_base : [P has \base base].

Definition feasible_dir (d: 'cV[R]_n) := false.
(*  let: 'P(A, _) := base in HPrim.feasible_dir A d.*)

Lemma feasible_dirP d :
  reflect (forall x, forall λ, x \in P -> λ >= 0 -> x + λ *: d \in P) (feasible_dir d).
Admitted.*)

Lemma feasible_dir_unbounded P c d :
  non_empty P -> feasible_dir d P -> '[c, d] < 0 ->
    ~~ bounded c P. (* RK *)
Proof.
move => non_empty_P /(feasible_dirP _ non_empty_P) feasible_dir_d_P d_decr_dir.
apply/contraT; rewrite negbK.
move/(bounded_lower_bound _ non_empty_P) => [K K_lower_bound].
move/non_emptyP: non_empty_P => [x x_in_P].
set λ := (K - '[ c, x] - 1) * ('[ c, d])^-1.
have λ_gt_0: 0 < λ.
  rewrite (ltr_ndivl_mulr _ _ d_decr_dir) mul0r subr_lt0.
  apply: (ler_lt_trans _ ltr01).
  rewrite subr_le0.
  exact: (K_lower_bound _ x_in_P).
move: (K_lower_bound _ (feasible_dir_d_P _ _ x_in_P (ltrW λ_gt_0))).
rewrite vdotDr vdotZr -mulrA mulVf;
  last by apply: ltr0_neq0.
by rewrite mulr1 -2!ler_subl_addl subrr oppr_ge0 lerNgt ltr01.
Qed.

Lemma compact_pointed P :
  non_empty P -> compact P ->
    pointed P. (* RK *)
Proof.
exact: HPrim.compact_pointed.
Qed.

End Pointedness.

Module Polytope.

Section Def.

Variable R : realFieldType.
Variable n : nat.

Inductive polytope := Polytope (P : 'poly[R]_n) of (compact P).
Coercion poly_of_polytope P := let: Polytope P' _ := P in P'.
Canonical polytope_subType := [subType for poly_of_polytope].
Definition polytope_eqMixin := Eval hnf in [eqMixin of polytope by <:].
Canonical polytope_eqType := Eval hnf in EqType polytope polytope_eqMixin.
Definition polytope_choiceMixin := [choiceMixin of polytope by <:].
Canonical polytope_choiceType := Eval hnf in ChoiceType polytope polytope_choiceMixin.

End Def.

Notation "''polyt[' R ]_ n" := (@polytope R n).
Notation "''polyt_' n" := ('polyt[_]_n).

Section BasicProp.

Variable R : realFieldType.
Variable n : nat.

Lemma polytope_compact (P : 'polyt[R]_n) : compact P.
Proof.
exact: valP.
Qed.

End BasicProp.

End Polytope.

Module FaceBase.

Section Def.

Variable R : realFieldType.
Variable n : nat.

Variable base : 'hpoly[R]_n.
Variable P : 'poly[R]_n.
Hypothesis P_base : [P has \base base].

Definition face_set :=
  ([fset '['P^=(base; I)] | I : {set 'I_(#ineq base)} & (({ eq P on base } \subset I) && non_empty '['P^=(base; I)])])%fset : {fset 'poly[R]_n}.

Definition face_empty :
  ~~ (non_empty P) -> face_set = fset0.
Proof.
move => P_empty; apply/fsetP => /= Q; rewrite in_fsetE /=.
apply/negbTE; move: P_empty; apply: contra.
move/imfsetP => /= [I] /andP [eqP_sub_I /non_emptyP [x x_in_Q]] _.
suff Q_subset_P: {subset '['P^=(base; I)] <= P} by apply/non_emptyP; exists x; apply: Q_subset_P.
apply/(subset_on_base (base := base)); try by done.
- exact: hpolyEq_base.
- by apply/(subset_trans eqP_sub_I)/activeP.
Qed.

End Def.

Section FaceP.

Variable R : realFieldType.
Variable n : nat.

Lemma faceP (base: 'hpoly[R]_n) (P Q : 'poly[R]_n) :
  [P has \base base ] -> non_empty P ->
    reflect (exists c, bounded c P /\ { over P, Q argmin c })
            (Q \in (face_set base P)).
Proof.
case: base => [m A b] P_base P_non_empty.
apply/(iffP idP).
- move/imfsetP => [J] /and3P [_ eqP_sub_J Q_non_empty] Q_repr.
  move/hpoly_of_baseP: P_base => P_repr.
  rewrite {}P_repr non_empty_quotP in P_non_empty *.
  rewrite non_empty_quotP in Q_non_empty *.
  set I := ({eq P}) in eqP_sub_J *.

  pose u := col_mx (\col_i (if i \in J then 1 else 0)) 0: 'cV[R]_(m+#|I|).
  have u_ge0 : u >=m 0.
  + rewrite col_mx_gev0 lev_refl andbT.
    apply/gev0P => i; rewrite mxE.
    case: ifP => [_|_]; [exact: ler01 | exact: lerr].
  have u_i_gt0 : forall i, (u (lshift #|I| i) 0 > 0) = (i \in J).
  + move => i; rewrite col_mxEu mxE.
    case: ifP => [_|_]; [exact: ltr01 | exact: ltrr].

  pose AI := col_mx A (-(row_submx A I)).
  pose bI := col_mx b (-(row_submx b I)).
  pose c := AI^T *m u; exists c.
  have c_bounded : HPrim.bounded c 'P^=(A, b; I) by exact: HPrim.normal_cone_bounded.

  have opt_val: HPrim.opt_value c_bounded = '[bI, u].
  move/HPrim.bounded_opt_value: (c_bounded) => [[x [x_in_P <-]] x_opt].
  apply/eqP; rewrite eqr_le; apply/andP; split; last first.
    * exact: HPrim.normal_cone_lower_bound.
    * move/HPrim.non_emptyP: Q_non_empty => [y y_in_Q].
      suff <-: '[c,y] = '[bI,u].
      - apply: x_opt; exact: (hpolyEq_antimono eqP_sub_J).
      - rewrite -vdot_mulmx mul_col_mx !vdot_col_mx vdot0l vdot0r !addr0.
        apply: eq_bigr => i _; rewrite mxE.
        case: ifP => [ i_in_J | _]; last by rewrite mulr0 mul0r.
        rewrite mul1r mulr1; exact: (hpolyEq_act y_in_Q).
  split; first by rewrite lp_quotE.
  move => x; split.
  + move/minimize_quotP/(HPrim.opt_valueP c_bounded); rewrite opt_val.
    move/andP => [x_in_PAbI].
    move/(HPrim.opt_value_csc u_ge0 x_in_PAbI) => x_csc.
    rewrite Q_repr mem_quotP; apply/hpolyEq_inP.
    split; first exact: (hpolyEq_antimono0 x_in_PAbI).
    move => j; rewrite -u_i_gt0; move/x_csc.
    by rewrite mul_col_mx !col_mxEu => ->.
  + rewrite Q_repr mem_quotP; move => x_in_PAbJ. (* TODO: the rewrite mem_quotP takes time, why? *)
    apply/minimize_quotP/(HPrim.opt_valueP c_bounded); rewrite opt_val.
    have x_in_PAbI : x \in 'P^=(A, b; I) by exact: (hpolyEq_antimono eqP_sub_J).
    apply/andP; split; first by done.
    apply/(HPrim.opt_value_csc u_ge0 x_in_PAbI) => i; rewrite mxE.
      case: (splitP' i) => [i' -> |?]; rewrite mxE; last by rewrite ltrr.
      case: ifP => [i'_in_J _ | ?]; last by rewrite ltrr.
      rewrite mul_col_mx !col_mxEu; exact: (hpolyEq_act x_in_PAbJ).

- move/hpoly_of_baseP: P_base => P_repr.
  move => [c] [c_bounded c_opt].
  (*apply/andP; split.
  + *)
  set I := ({eq P}) in P_repr *. (* TODO: parsing error if parenthesis are removed *)
  suff: exists (J: {set 'I_(#ineq 'P(A, b))}), (I \subset J /\ Q = '['P^=(A, b; J)]).
  + move => [J] [I_sub_J Q_eq_PabJ].
    apply/imfsetP; exists J; last by done.
    rewrite /= inE; apply/andP; split; first by done.
    move/boundedP: c_bounded => [x /c_opt x_in_Q].
    by rewrite -Q_eq_PabJ; apply/non_emptyP; exists x.
  + rewrite P_repr non_empty_quotP !lp_quotE in P_non_empty c_bounded c_opt.
    move/HPrim.dual_opt_sol: (c_bounded) => [u] [u_ge0 c_eq c_optval].
    pose J := I :|: [set i | (usubmx u) i 0 > 0].
    exists J; split; first exact: subsetUl.
    suff PAbJ_eq_Q : 'P^=(A, b; J) =i Q. (* we should introduce a lemma for that: P = '[Q] <-> P =i Q *)
    * case: (hpolyP Q) => [Q' Q_eq_Q'].
      rewrite Q_eq_Q'; apply/poly_eqP => x.
      by rewrite PAbJ_eq_Q Q_eq_Q' mem_quotP.
    * move => x; apply/idP/idP => [x_in_PAbJ | x_in_Q].
      - have x_in_PAbI : x \in 'P^=(A, b; I).
        move: x_in_PAbJ; apply/hpolyEq_antimono; exact: subsetUl.
        apply/c_opt/minimize_quotP/HPrim.opt_valueP/andP; split; first by done.
        rewrite -c_optval c_eq; apply/(HPrim.opt_value_csc u_ge0 x_in_PAbI) => i.
        case: (splitP' i) => [j -> | j -> _].
        + rewrite -[u]vsubmxK mul_col_mx !col_mxEu => u_j_gt0.
          have j_in_J : (j \in J) by rewrite !inE; apply/orP; right.
          exact: (hpolyEq_act x_in_PAbJ).
        + rewrite mul_col_mx !col_mxEd mulNmx -row_submx_mul.
          rewrite 2![in LHS]mxE 2![in RHS]mxE.
          apply: congr1; apply: (hpolyEq_act x_in_PAbI); exact: enum_valP.
      - move/c_opt/minimize_quotP/(HPrim.opt_valueP c_bounded)/andP: x_in_Q => [x_in_PAbI].
        rewrite {1}c_eq -c_optval; move/(HPrim.opt_value_csc u_ge0 x_in_PAbI) => x_act.
        apply/hpolyEq_inP; split; first exact: (hpolyEq_antimono0 x_in_PAbI).
        move => j; rewrite inE; case/orP => [j_in_I | u_j_gt0].
        + exact: (hpolyEq_act x_in_PAbI).
        + rewrite inE mxE in u_j_gt0.
          by move/(_ _ u_j_gt0): x_act; rewrite mul_col_mx !col_mxEu.
Qed.

End FaceP.

End FaceBase.

Arguments FaceBase.faceP [_ _ _ _ _].

Section Face.

Variable R : realFieldType.
Variable n : nat.

Definition face_set (P : 'poly[R]_n) := FaceBase.face_set (hpoly P) P.

Notation "\face P" := (face_set P).

Lemma face_empty (P : 'poly[R]_n) : ~~ (non_empty P) -> \face P = fset0.
Proof.
apply: FaceBase.face_empty; exact: hpoly_base.
Qed.

Lemma face_baseP (P Q : 'poly[R]_n) (base : 'hpoly[R]_n) :
  [P has \base base] ->
    reflect ([/\ has_base Q base, { eq P on base } \subset { eq Q on base } & non_empty Q ])
            (Q \in \face P).
Proof.
move => P_base.
suff ->: (Q \in \face P) = (Q \in (FaceBase.face_set base P)).
- apply: (iffP idP).
  + move/imfsetP => [J] /and3P [_ eqP_sub_J Q_non_empty] ->; split; last by done.
    * exact: hpolyEq_base.
    * by apply: (subset_trans eqP_sub_J); apply: activeP.
  + move => [Q_base eqP_sub_eqQ Q_non_empty].
    apply/imfsetP; exists {eq Q on base}; last exact: hpoly_of_baseP.
    * by rewrite inE /=; apply/andP; split; last by rewrite -hpoly_of_baseP.
case: (boolP (non_empty P)) => [ P_non_empty | P_empty ].
- apply/(sameP (FaceBase.faceP (hpoly_base _) P_non_empty)); try by done.
  + exact: FaceBase.faceP.
- move/face_empty: (P_empty) ->.
  by move/FaceBase.face_empty: P_empty ->.
Qed.

Arguments face_baseP [P Q base].

Lemma face_hpolyEqP (base : 'hpoly[R]_n) I J :
  let P := '['P^=(base; I)] in
  let Q := '['P^=(base; J)] in
  (Q \in \face P) = (J \subset I).
Admitted.

Lemma face_hpolyEq0P (base : 'hpoly[R]_n) J :
  '[ 'P^=(base; J) ] \in \face('[base]).
Admitted.


Lemma face_has_base (P Q : 'poly[R]_n) (base : 'hpoly[R]_n) :
  [P has \base base] -> Q \in \face P -> [Q has \base base].
Proof.
by move => P_base /(face_baseP P_base) => [[?]].
Qed.

Lemma faceP (P Q : 'poly[R]_n) :
  non_empty P ->
    reflect (exists c, bounded c P /\ { over P, Q argmin c })
            (Q \in \face P).
Proof.
move => P_non_empty.
apply/FaceBase.faceP; by [done | exact: hpoly_base].
Qed.

Lemma face_of_face (P Q: 'poly[R]_n) :
  Q \in (\face P) -> (\face Q `<=` \face P)%fset.
Proof.
move/(face_baseP (hpoly_base _)).
set base := (hpoly P).
move => [Q_base eqP_sub_eqQ _].
apply/fsubsetP => Q' /(face_baseP Q_base) [Q'_base eqQ_sub_eqQ' Q'_non_empty].
apply/(face_baseP (hpoly_base _)); split; try by done.
by apply/(subset_trans _ eqQ_sub_eqQ').
Qed.

Fact self_face (P : 'poly[R]_n) :
  non_empty P -> P \in \face P. (* RK *)
Proof.
move => P_non_empty; apply/(face_baseP (hpoly_base P)); split;
  by [exact: hpoly_base | exact: subxx | done].
Qed.

Fact face_subset (P Q : 'poly[R]_n) :
  Q \in \face P -> {subset Q <= P}. (* RK *)
Proof.
move/(face_baseP (hpoly_base P)) => [Q_has_base ? _].
by apply: (subset_on_base Q_has_base (hpoly_base P)).
Qed.

Lemma compact_face P F :
  compact P -> F \in \face P -> compact F.
Proof. (* RK *)
move/compactP_Linfty => [K bounded_on_P].
move => F_is_face_of_P.
apply/compactP_Linfty; exists K.
move => x x_in_F i.
exact: (((bounded_on_P x) ((face_subset F_is_face_of_P) _ x_in_F)) i).
Qed.


Fact face_of_face_incl_rel (P F : 'poly[R]_n) :
  F \in \face P -> \face F = [fset F' in \face P | (F' <= F)%PH]%fset.
Proof.
move => F_face_P.
apply/eqP; rewrite eqEfsubset; apply/andP; split; apply/fsubsetP.
- move => F' F'_face_F.
  rewrite in_fsetE inE; apply/andP; split.
  + by move/fsubsetP/(_ _ F'_face_F): (face_of_face F_face_P).
  + apply/poly_subsetP; exact: face_subset.
- move => F'; rewrite in_fsetE inE => /andP [F'_face_P /poly_subsetP F'_sub_F].
  move/(face_baseP (hpoly_base P)): F_face_P => [F_base eqP_sub_eqF F_non_empty].
  move/(face_baseP (hpoly_base P)): F'_face_P => [F'_base eq_P_sub_eq_F' F'_non_empty].
  apply/(face_baseP F_base); split.
  + exact: F'_base.
  + by apply/(subset_on_base F'_base F_base).
  + exact: F'_non_empty.
Qed.

Fact has_face_imp_non_empty (P Q : 'poly[R]_n) :
  Q \in \face P -> non_empty P. (* RK *)
Proof.
move => Q_is_face_of_P.
apply: contraT => empty_P.
by rewrite (face_empty empty_P) in Q_is_face_of_P.
Qed.

Fact face_is_non_empty (P Q : 'poly[R]_n) :
  Q \in \face P -> non_empty Q. (* RK *)
Proof.
move => Q_is_face_of_P.
by move: (face_baseP (hpoly_base P) Q_is_face_of_P) => [_ _ ?].
Qed.

Lemma polyI_face_is_face (P F F' : 'poly[R]_n) :
  (F \in \face P) -> (F' \in \face P) -> non_empty (F && F')%PH ->
    (F && F')%PH \in \face P. (* RK: Proposition 2.3 (ii) of Ziegler's book *)
Proof.
move => /(face_baseP (hpoly_base P)) [F_base eq_P_subset_eq_F _].
move => /(face_baseP (hpoly_base P)) [F'_base eq_P_subset_eq_F' _].
move => non_empty_polyI.
apply/(face_baseP (hpoly_base P)).
split.
- exact: (polyI_same_base F_base F'_base).
- apply: (subset_trans _ polyI_eq_same_base).
  rewrite -[{eq(P) on _}]setUid.
  exact: (setUSS eq_P_subset_eq_F eq_P_subset_eq_F').
- exact: non_empty_polyI.
Qed.

Lemma feasible_basic_point_vertex (hP : 'hpoly[R]_n) (v : 'cV[R]_n) :
  (feasible_basic_point hP v) = ([poly v] \in \face '[hP]). (* RK *)
Proof.
case: hP => m A b.
apply/idP/idP => [v_is_feasible_basic_point | poly_v_is_face].
- have non_empty_hP: non_empty '['P(A, b)].
    apply/non_emptyP; exists v; rewrite mem_quotP.
    exact: (proj1 (andP v_is_feasible_basic_point)).
  move/feasible_basic_pointP: v_is_feasible_basic_point => [bas [bas_is_feasible v_eq]].
  apply/(faceP _ non_empty_hP).
  exists (Simplex.obj_of_basis (Simplex.FeasibleBasis bas_is_feasible)).
  split.
  + apply/bounded_lower_bound; first exact: non_empty_hP.
    exists '[Simplex.obj_of_basis (Simplex.FeasibleBasis bas_is_feasible), Simplex.point_of_basis b bas].
    move => y y_in_hP.
    apply/contraT.
    rewrite -ltrNge => s_ineq.
    rewrite mem_quotP in y_in_hP.
    move: (Simplex.obj_of_basisP y_in_hP (ltrW s_ineq)) => y_eq.
    by rewrite y_eq ltrr in s_ineq.
  + have v_in_hP: Simplex.point_of_basis b bas \in '['P(A, b)].
      rewrite mem_quotP Simplex.polyhedron_equiv_lex_polyhedron.
      exact: (Simplex.feasible_basis_is_feasible (Simplex.FeasibleBasis bas_is_feasible)).
    move => y; rewrite v_eq.
    split.
    * rewrite {1}mem_quotP.
      move => [y_in_hP y_min].
      apply/poly_point_inP.
      by apply/(Simplex.obj_of_basisP y_in_hP ((y_min (Simplex.point_of_basis b bas)) v_in_hP)).
    * move/poly_point_inP => ->.
      split; first exact: v_in_hP.
      move => w w_in_hP.
      apply/contraT.
      rewrite -ltrNge => s_ineq.
      rewrite mem_quotP in w_in_hP.
      move: (Simplex.obj_of_basisP w_in_hP (ltrW s_ineq)) => w_eq.
      by rewrite w_eq ltrr in s_ineq.
- move/(faceP _ (has_face_imp_non_empty poly_v_is_face)): poly_v_is_face => [c [bounded_c_hP v_min]].
  apply/andP; split.
  + rewrite -mem_quotP.
    suff: {over '['P(A, b)], v minimizes c} by move/proj1.
    by apply/(v_min v)/poly_point_inP.
  + apply/contraT => Hrk.
    have v_in_hP: v \in 'P(A, b).
      suff : {over '['P(A, b)], v minimizes c} by move/proj1; rewrite mem_quotP.
      by apply/(v_min v)/poly_point_inP.
    pose AI := row_submx A (Simplex.active_ineq A b v).
    have: (kermx AI^T != 0).
      rewrite kermx_eq0 -row_leq_rank -ltnNge ltn_neqAle.
      apply/andP; split.
      * rewrite mxrank_tr neq_ltn.
        apply/orP; left.
        by rewrite -ltnNge in Hrk.
      * by apply: rank_leq_row.
    move/rowV0Pn => [w /sub_kermxP/(congr1 trmx) Hw w_neq_0].
    rewrite trmx0 trmx_mul trmxK in Hw.
    rewrite {Hrk}.
    pose gap_seq := [seq (if (A *m w^T) i 0 == 0 then 1 else ( ((A *m v) i 0 - b i 0 )) * ( `|(A *m w^T) i 0 |)^-1 ) |
      i <- enum 'I_m & i \notin (Simplex.active_ineq A b v)].
    pose epsilon := if nilp gap_seq then 1 else (min_seq gap_seq 1).
  have epsilon_gt_0 : epsilon > 0.
    rewrite /epsilon; case: ifP => [ _ | /nilP ?]; first by apply: ltr01.
    rewrite min_seq_positive; last by right; apply: ltr01.
    apply/allP => epsilon'.
    rewrite /gap_seq; move/mapP => [i]; rewrite mem_filter; move/andP => [i_not_in_active _].
    case: ifP => [_ -> | /negbT ? ->]; first by apply: ltr01.
      apply: divr_gt0; last by rewrite normr_gt0.
      rewrite subr_gt0 ltr_def.
      apply/andP; split; last by move/forallP: v_in_hP => Hv; move/(_ i): Hv.
      by rewrite in_set in i_not_in_active.
  have not_in_active_ineq:
    (forall i, i \notin (Simplex.active_ineq A b v) -> (A *m v) i 0 - epsilon *  `| (A *m w^T) i 0 | >= b i 0).
    move => i ?.
    have Hgap_seq: (~~ nilp gap_seq).
      rewrite /gap_seq /nilp size_map; apply/nilP/eqP.
      rewrite -has_filter.
      by apply/hasP; exists i; first by rewrite mem_enum.
    case Hwi: ((A *m w^T) i 0 == 0); first by move/eqP: Hwi => ->; rewrite normr0 mulr0 subr0; move/forallP/(_ i): v_in_hP.
      rewrite ler_subr_addr addrC -ler_subr_addr.
      rewrite -ler_pdivl_mulr; last by rewrite normr_gt0 //; apply: negbT.
      rewrite /epsilon ifF; last by apply: negbTE.
      apply: min_seq_ler.
      rewrite /gap_seq.
      apply/mapP; exists i.
      rewrite mem_filter; apply/andP; split; by [done | rewrite mem_enum].
      by rewrite Hwi.
  pose y := v + epsilon *: w^T.
  pose z := v - epsilon *: w^T.
  have y_in_hP: y \in 'P(A, b).
    apply/forallP => i; rewrite /y mulmxDr -scalemxAr mxE [X in _ + X]mxE.
    case: (boolP (i \in (Simplex.active_ineq A b v))) => [i_in_active | i_not_in_active].
    * move/colP/(_ (enum_rank_in i_in_active i)): Hw; rewrite [RHS]mxE -row_submx_mul row_submx_mxE enum_rankK_in //; move ->.
      by rewrite mulr0 addr0; move/forallP: v_in_hP.
    * have ineq: (A *m v) i 0 + epsilon * (A *m w^T) i 0 >= (A *m v) i 0 - epsilon * `|(A *m w^T) i 0|
        by rewrite (ler_add2l ((A *m v) i 0)) -[X in X * `|_|]gtr0_norm // -normrM ler_oppl -normrN; apply: ler_norm.
      by move: (not_in_active_ineq i i_not_in_active) ineq; apply: ler_trans.
  have z_in_hP: z \in 'P(A, b).
    apply/forallP => i; rewrite /z mulmxDr -scaleNr -scalemxAr scaleNr mxE [X in _ + X]mxE [X in _ - X]mxE.
    case: (boolP (i \in (Simplex.active_ineq A b v))) => [i_in_active | i_not_in_active].
    * move/colP/(_ (enum_rank_in i_in_active i)): Hw; rewrite [RHS]mxE -row_submx_mul row_submx_mxE enum_rankK_in //; move ->.
      by rewrite mulr0 subr0; move/forallP: v_in_hP.
    * have ineq: (A *m v) i 0 - epsilon * (A *m w^T) i 0 >= (A *m v) i 0 - epsilon * `|(A *m w^T) i 0|
        by rewrite (ler_add2l ((A *m v) i 0)) -[X in X * `|_|]gtr0_norm // -normrM ler_opp2; apply: ler_norm.
      by move: (not_in_active_ineq i i_not_in_active) ineq; apply: ler_trans.
  case: (boolP ('[c ,w^T]==0)) => [/eqP eq_0 | neq_0].
  * have: z == v.
      apply/eqP/poly_point_inP/(v_min z)/opt_valueP/andP; split; first by rewrite mem_quotP.
      move/poly_point_inP/(v_min v)/(opt_valueP bounded_c_hP)/andP/proj2/eqP: (erefl v) <-.
      by rewrite vdotBr vdotZr eq_0 mulr0 subr_eq addr0.
    rewrite subr_eq addrC -subr_eq addrN eq_sym scaler_eq0 -[(epsilon == 0)]negbK -[(w^T == 0)]negbK -negb_and.
    suff ->: (epsilon != 0) && (w^T != 0) by done.
    apply/andP; split; first by apply: lt0r_neq0.
    move: w_neq_0.
    apply/contra.
    rewrite -trmx0.
    move/eqP => H.
    by apply/eqP/trmx_inj.
  * rewrite neqr_lt in neq_0.
    case: (orP neq_0) => [lt_0 | gt_0].
    - suff : '[ c, y] < '[ c, v].
        move/poly_point_inP/(v_min v)/(opt_valueP bounded_c_hP)/andP/proj2/eqP: (erefl v) ->.
        rewrite -mem_quotP in y_in_hP.
        by rewrite ltrNge ((proj2 (bounded_opt_value bounded_c_hP)) _ y_in_hP).
      by rewrite vdotDr addrC -ltr_subr_addr addrN vdotZr (pmulr_rlt0 _ epsilon_gt_0).
    - suff : '[ c, z] < '[ c, v].
        move/poly_point_inP/(v_min v)/(opt_valueP bounded_c_hP)/andP/proj2/eqP: (erefl v) ->.
        rewrite -mem_quotP in z_in_hP.
        by rewrite ltrNge ((proj2 (bounded_opt_value bounded_c_hP)) _ z_in_hP).
      by rewrite vdotDr addrC -ltr_subr_addr addrN vdotNr oppr_lt0 vdotZr (pmulr_rgt0 _ epsilon_gt_0).
Qed.

Variable P : 'poly[R]_n.
Variable c : 'cV[R]_n.
Hypothesis c_bounded : bounded c P.

(*Definition face_of_obj := (* this should be defined by using a proper intersection operation *)
  let: 'P(A, b) := hpoly P in
  let A' := col_mx c^T A in
  let b' := col_mx ((opt_value c_bounded)%:M) b in
    '[ 'P^=(A', b'; [set ord0]) ].*)
Definition face_of_obj := polyI P (poly_hyperplane c (opt_value c_bounded)).

Fact face_of_objP x :
  reflect ({ over P, x minimizes c }) (x \in face_of_obj).
Proof. (* RK *)
rewrite polyI_inE poly_hyperplane_inE.
apply: (iffP idP) => [/andP [x_in_P x_optimal] | /opt_valueP H].
- by apply/opt_valueP/andP; split.
- move/andP: (H c_bounded) => [x_in_P x_optimal].
  by apply/andP; split.
Qed.

Arguments face_of_objP [x].

Hypothesis P_non_empty : non_empty P.

Lemma face_of_obj_face :
  face_of_obj \in \face P.
Proof.
apply/faceP; first by done.
exists c; split; first by done.
move => x; exact: (rwP face_of_objP).
Qed.

End Face.

Arguments face_baseP [R n P Q base].

Notation "\face P" := (face_set P).

Arguments non_emptyP [R n P].
Arguments faceP [R n P Q].