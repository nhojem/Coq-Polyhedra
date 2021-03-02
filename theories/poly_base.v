(* --------------------------------------------------------------------
 * Copyright (c) - 2017--2020 - Xavier Allamigeon <xavier.allamigeon at inria.fr>
 * Copyright (c) - 2017--2020 - Ricardo D. Katz <katz@cifasis-conicet.gov.ar>
 * Copyright (c) - 2019--2020 - Pierre-Yves Strub <pierre-yves@strub.nu>
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
Require Import Recdef.
From mathcomp Require Import all_ssreflect ssralg ssrnum zmodp matrix mxalgebra vector finmap.

From lattice Require Import extra_misc xbigop finlattice.
Require Import extra_misc inner_product extra_matrix (*xorder*) vector_order row_submx.
Require Import hpolyhedron polyhedron barycenter.

Import Order.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope poly_scope.
Import GRing.Theory Num.Theory.


(* -------------------------------------------------------------------- *)
Section PointedType.
Context (R : realFieldType) (n : nat).

Record pointedPoly : predArgType :=
  Pointed { pointed_poly :> 'poly[R]_n; _ : pointed pointed_poly }.

Canonical pointedPoly_subType := Eval hnf in [subType for pointed_poly].
Definition pointedPoly_eqMixin := Eval hnf in [eqMixin of pointedPoly by <:].
Canonical pointedPoly_eqType := Eval hnf in EqType pointedPoly pointedPoly_eqMixin.
Definition pointedPoly_choiceMixin := Eval hnf in [choiceMixin of pointedPoly by <:].
Canonical pointedPoly_choiceType := Eval hnf in ChoiceType pointedPoly pointedPoly_choiceMixin.

Definition pointedPoly_of of phant R := pointedPoly.
Identity Coercion type_pointedPoly_of : pointedPoly_of >-> pointedPoly.
End PointedType.

Bind Scope ring_scope with pointedPoly_of.
Bind Scope ring_scope with pointedPoly.

Reserved Notation "''pointed[' R ]_ n"
  (at level 8, n at level 2, format "''pointed[' R ]_ n").

Notation "''pointed[' R ]_ n" := (@pointedPoly_of _ n (Phant R)).

Section PointedTheory.
Context {R : realFieldType} (n : nat).

Canonical pointedPoly_of_subType := Eval hnf in [subType of 'pointed[R]_n].
Canonical pointedPoly_of_eqType := Eval hnf in [eqType of 'pointed[R]_n].
Canonical pointedPoly_of_choiceType := Eval hnf in [choiceType of 'pointed[R]_n].

Lemma pointed_slice (P : 'pointed[R]_n) e : pointed (slice e P).
Proof. by apply/(pointedS _ (valP P))/le_slice. Qed.
Canonical pointed_slice_pointed (P : 'pointed[R]_n) e := Pointed (pointed_slice P e).

End PointedTheory.

(* -------------------------------------------------------------------- *)
Section CompactType.
Context (R : realFieldType) (n : nat).

Record compactPoly : predArgType :=
  mkCompact { compact_poly :> 'pointed[R]_n; _ : compact compact_poly }.

Canonical compactPoly_subType := Eval hnf in [subType for compact_poly].
Definition compactPoly_eqMixin := Eval hnf in [eqMixin of compactPoly by <:].
Canonical compactPoly_eqType := Eval hnf in EqType compactPoly compactPoly_eqMixin.
Definition compactPoly_choiceMixin := Eval hnf in [choiceMixin of compactPoly by <:].
Canonical compactPoly_choiceType := Eval hnf in ChoiceType compactPoly compactPoly_choiceMixin.

Definition compactPoly_of of phant R := compactPoly.
Identity Coercion type_compactPoly_of : compactPoly_of >-> compactPoly.
End CompactType.

Bind Scope ring_scope with compactPoly_of.
Bind Scope ring_scope with compactPoly.

Reserved Notation "''compact[' R ]_ n"
  (at level 8, n at level 2, format "''compact[' R ]_ n").

Notation "''compact[' R ]_ n" := (@compactPoly_of _ n (Phant R)).

Section CompactTheory.
Context {R : realFieldType} (n : nat).

Canonical compactPoly_of_subType := Eval hnf in [subType of 'compact[R]_n].
Canonical compactPoly_of_eqType := Eval hnf in [eqType of 'compact[R]_n].
Canonical compactPoly_of_choiceType := Eval hnf in [choiceType of 'compact[R]_n].

End CompactTheory.

(* -------------------------------------------------------------------- *)
Section CompactPointed.
Context (R : realFieldType) (n : nat) .

Definition Compact (P : 'poly[R]_n) (cp : compact P) :=
  @mkCompact R n (Pointed (compact_pointed cp)) cp.

Lemma compact_slice (P : 'poly[R]_n) e :
  compact P -> compact (slice e P).
Proof. move=> P_compact; by apply/(subset_compact P_compact)/le_slice. Qed.
Canonical compact_slice_compact (P : 'compact[R]_n) e :=
  Compact (compact_slice e (valP P)).
End CompactPointed.

(* -------------------------------------------------------------------- *)
(*Section PolyPO.
Context (R : realFieldType) (n : nat).

Implicit Types P Q : 'poly[R]_n.

Definition pointedPoly_porderMixin := [porderMixin of @pointedPoly R n by <:].
Canonical pointedPoly_porderType :=
  Eval hnf in POrderType ring_display (@pointedPoly R n) pointedPoly_porderMixin.

Definition pointedPoly_of_porderType :=
  Eval hnf in [porderType of 'pointed[R]_n].
End PolyPO.*)

(* -------------------------------------------------------------------- *)
Section PolyBase.

Variable (R : realFieldType) (n : nat).

Section FixedBase.

Definition has_base (base : base_t[R,n]) (P : 'poly[R]_n) :=
  (P `>` [poly0]) ==>
    [exists I : {fsubset base}, P == 'P^=(base; I)].

Notation "'[' P 'has' '\base' base ']'" := (has_base base P) : poly_scope.

Context {base : base_t[R,n]}.

Lemma has_baseP {P : 'poly[R]_n} :
  reflect ((P `>` [poly0]) -> exists I : {fsubset base}, P = 'P^=(base; I)) [P has \base base].
Proof.
by apply/(iffP implyP) => [H /H /exists_eqP [I ->]| H /H [I ->]];
  [|apply/exists_eqP]; exists I.
Qed.

Inductive poly_base := PolyBase { pval :> 'poly[R]_n ; _ : [pval has \base base]}.
Canonical poly_base_subType := [subType for pval].
Definition poly_base_eqMixin := Eval hnf in [eqMixin of poly_base by <:].
Canonical poly_base_eqType := Eval hnf in EqType poly_base poly_base_eqMixin.
Definition poly_base_choiceMixin := Eval hnf in [choiceMixin of poly_base by <:].
Canonical poly_base_choiceType := Eval hnf in ChoiceType poly_base poly_base_choiceMixin.

(*
Definition poly_base_porderMixin := [porderMixin of poly_base by <:].
Canonical poly_base_porderType :=
  Eval hnf in POrderType polyh_display poly_base poly_base_porderMixin.
*)

Lemma pvalP (P : poly_base) : [pval P has \base base].
Proof.
by apply/valP.
Qed.

Lemma pval_inj : injective pval.
Proof.
by apply/val_inj.
Qed.

Lemma poly0_baseP : [ [poly0] has \base base].
Proof.
by rewrite /has_base RT.ltxx.
Qed.
Canonical poly0_base := PolyBase poly0_baseP.

End FixedBase.

Notation "'[' P 'has' '\base' base ']'" := (has_base base P) : poly_scope.
Notation "'{poly'  base '}'" := (@poly_base base) : poly_scope.
Definition poly_base_of base (x : {poly base}) & (phantom 'poly[R]_n x) : {poly base} := x.
Notation "P %:poly_base" := (poly_base_of (Phantom _ P)) (at level 0) : poly_scope.

Lemma polyEq_baseP base I :
  (I `<=` base)%fset -> [('P^=(base; I)) has \base base].
Proof.
move => Isub.
by apply/implyP => _; apply/exists_eqP => /=; exists (I %:fsub).
Qed.

Canonical polyEq_base base I (H : expose (I `<=` base)%fset) := PolyBase (polyEq_baseP H).

Variable base : base_t[R,n].

Variant poly_base_spec (P : {poly base}) : Prop :=
| PolyBase0 of (P = ([poly0])%:poly_base) : poly_base_spec P
| PolyBaseN0 (I : {fsubset base}) of (P = 'P^=(base; I)%:poly_base /\ P `>` [poly0]) : poly_base_spec P.

Lemma poly_baseP (P : {poly base}) : poly_base_spec P.
Proof.
case: (emptyP P) => [/pval_inj -> | P_prop0]; first by constructor.
move/implyP/(_ P_prop0)/exists_eqP: (pvalP P) => [I ?].
constructor 2 with I.
split; [exact: val_inj | done].
Qed.

Lemma poly_base_subset (P : {poly base}) :
  pval P `<=` 'P(base).
Proof.
case/poly_baseP : (P) => [->| I [-> _]];
  [ exact: RT.le0x | exact: polyEq_antimono0].
Qed.

Lemma poly_base_subset_hs (P : {poly base}) e :
  e \in base -> pval P `<=` [hs e].
Proof.
move => ?; apply/(RT.le_trans (poly_base_subset _)).
exact: poly_of_base_subset_hs.
Qed.

Definition set_of_poly_base (P : {poly base}) : option {fsubset base} :=
  if @idP (P `>` ([poly0])) is ReflectT H then
    let I := xchoose (existsP (implyP (pvalP P) H)) in
    Some I
  else
    None.

Definition set_of_poly_base_pinv (I : option {fsubset base}) : {poly base} :=
  match I with
  | Some I' =>
    let P := 'P^=(base; I')%:poly_base in
    if set_of_poly_base P == Some I' then P else [poly0]%:poly_base
  | None => [poly0]%:poly_base
  end.

Lemma set_of_poly_baseK :
  cancel set_of_poly_base set_of_poly_base_pinv.
Proof.
move => P.
move: (erefl (set_of_poly_base P)).
rewrite {2 3}/set_of_poly_base.
case: {-}_/idP => [P_prop0 /=| /negP h _].
- set prop := existsP _; set I := xchoose _; set Q := 'P^=(base; I)%:poly_base.
  suff ->: P = Q.
  + by move => eq; rewrite /set_of_poly_base_pinv /Q ifT ?eq.
  + by apply/val_inj => /=; move/eqP: (xchooseP prop) ->.
- rewrite RT.lt0x negbK in h.
  by rewrite /=; apply/val_inj => /=; move/eqP: h ->.
Qed.

Definition poly_base_countMixin := CanCountMixin set_of_poly_baseK.
Canonical poly_base_countType := Eval hnf in CountType {poly base} poly_base_countMixin.
Definition poly_base_finMixin := CanFinMixin set_of_poly_baseK.
Canonical poly_base_finType := Eval hnf in FinType {poly base} poly_base_finMixin.
Canonical poly_base_subFinType := [subFinType of {poly base}].

Lemma poly_of_baseP :
  ['P(base) has \base base].
Proof.
suff ->: 'P(base) = 'P^=(base; fset0)%:poly_base by exact: pvalP.
by rewrite /= polyEq0.
Qed.
Canonical poly_of_base_base := PolyBase (poly_of_baseP).

Lemma polyI_baseP (P Q : {poly base}) :
  [pval P `&` pval Q has \base base].
Proof.
case: (poly_baseP P) => [->| I [-> _]]; first by rewrite /= RT.meet0x (valP ([poly0]%:poly_base)).
case: (poly_baseP Q) => [->| I' [-> _]]; first by rewrite /= RT.meetx0 (valP ([poly0]%:poly_base)).
apply/has_baseP => _; exists (I `|` I')%fset%:fsub; by rewrite polyEq_polyI.
Qed.
Canonical polyI_base P Q := PolyBase (polyI_baseP P Q).

Lemma slice_baseP (e : lrel) (P : {poly base}) :
  [(slice e P) has \base (e +|` base)].
Proof.
case: (poly_baseP P) => [->| I [-> _]]; first by rewrite /= slice0 (valP ([poly0]%:poly_base)).
apply/has_baseP => _.
by exists (e +|` I)%:fsub; rewrite slice_polyEq.
Qed.
Canonical slice_base e P := PolyBase (slice_baseP e P).

Lemma argmin_baseP (P : {poly base}) c :
  [(argmin P c) has \base base].
Proof.
(* we first suppose that flat_prop holds, ie this is the situation in which
 * P (here quantified as Q) would play the role of the base *)
suff flat_prop: forall base0, bounded ('P(base0) : 'poly[R]_n) c -> [(argmin ('P(base0) : 'poly[R]_n) c) has \base base0].
- apply/has_baseP; rewrite -bounded_argminN0.
  case/poly_baseP : (P) => [->| I [-> _]]; first by rewrite bounded_poly0.
  rewrite /= (polyEq_flatten _) => bounded_PI.
  move/flat_prop/has_baseP: (bounded_PI); rewrite -bounded_argminN0.
  move => /(_ bounded_PI) => [[J] ->].
  by move: (polyEq_of_polyEq J)
    => [K] ->; exists K.
- (* now this is the classic proof of Schrijver *)
  move => base0 c_bounded.
  move: (dual_opt_sol c_bounded) => [w w_ge0 w_comb].
  apply/has_baseP; exists (finsupp w)%:fsub.
  move: (opt_point c_bounded) => [x x_in_P0 c_x_eq_opt_val].
  have: x \in [hp (combine w)].
- by rewrite inE w_comb /=; apply/eqP.
  move/(compl_slack_cond w_ge0 x_in_P0) => x_in_P0I.
  have ->: c = (combine w).1 by rewrite w_comb.
  apply/dual_sol_argmin; try by done.
  by apply/proper0P; exists x.
Qed.
Canonical argmin_base (P : {poly base}) c := PolyBase (argmin_baseP P c).

Lemma affine_base : [(affine << base >>) has \base base].
Proof.
by rewrite -polyEqT_affine pvalP.
Qed.
Canonical affine_baseP := PolyBase affine_base.

End PolyBase.

Notation "'{poly'  base '}'" := (@poly_base _ _ base) : poly_scope.
Notation "P %:poly_base" := (poly_base_of (Phantom _ P)) (at level 0) : poly_scope.
Notation "'[' P 'has' '\base' base ']'" := (has_base base P) : poly_scope.

Module BaseQuotient.
Section BaseQuotient.

Variable (R : realFieldType) (n : nat).

Lemma poly_has_base P :
  exists (x : { base : base_t[R,n] & {poly base}}),
    P == (tagged x) :> 'poly[R]_n.
Proof.
move: (is_poly_of_base P) => [base /eqP ->].
by exists (Tagged _ ('P(base)%:poly_base : {poly base})) => /=.
Qed.

Definition of_poly (P : 'poly[R]_n) :=
  xchoose (poly_has_base P).
Definition to_poly (x : { base : base_t[R,n] & {poly base} })
  := pval (tagged x).

Lemma of_polyK : cancel of_poly to_poly.
Proof.
move => P; rewrite /of_poly; symmetry; apply/eqP.
exact: (xchooseP (poly_has_base _)).
Qed.

Definition base_quot_class := QuotClass of_polyK.

Canonical base_quot := QuotType 'poly[R]_n base_quot_class.

Definition repr_base (P : 'poly[R]_n) := (tag (repr P)).
Definition repr_poly_base (P : 'poly[R]_n) : {poly (repr_base P)} := tagged (repr P).

Lemma repr_baseP P : [P has \base (repr_base P)].
Proof.
rewrite -{-1}[P]reprK unlock; exact: pvalP.
Qed.
(*Canonical poly_base_repr_baseP (P : 'poly[R]_n) := PolyBase (repr_baseP P).*)

End BaseQuotient.
Module Import Exports.
Canonical base_quot.
(*Canonical poly_base_repr_baseP.*)
End Exports.
End BaseQuotient.

Export BaseQuotient.Exports.

Notation "\repr_base P" := (BaseQuotient.repr_base P) (at level 40).
Notation "\repr P" := (BaseQuotient.repr_poly_base P) (at level 40).

Section BaseQuotientAux.

Variable (R : realFieldType) (n : nat).

Lemma reprK (P : 'poly[R]_n) : \repr P = P :> 'poly[R]_n.
Proof.
by rewrite -[P in RHS]reprK [in RHS]unlock.
Qed.

Lemma polybW (Pt : 'poly[R]_n -> Prop) :
  (forall (base : base_t[R,n]) (Q : {poly base}), Pt Q) -> (forall P : 'poly[R]_n, Pt P).
Proof.
by move => ? P; rewrite -[P]reprK.
Qed.

Lemma non_redundant_baseW (Pt : 'poly[R]_n -> Prop) :
  (forall (base : base_t[R,n]), non_redundant_base base -> Pt 'P(base)%:poly_base)
    -> (forall P : 'poly[R]_n, Pt P).
Proof.
move => h P.
move: (is_poly_of_base P) => [base /eqP ->].
rewrite -poly_of_non_redundant_base.
have ->: 'P(mk_non_redundant_base base) = 'P(mk_non_redundant_base base)%:poly_base by [].
by apply/h/mk_non_redundant_baseP.
Qed.

End BaseQuotientAux.

Section PolyBaseFace.

Variable (R : realFieldType) (n : nat) (base : base_t[R,n]).

Definition pb_face_set (P : {poly base}) : {set {poly base}} :=
  [set Q : {poly base} | pval Q `<=` pval P].

Notation "\face_set P" := (pb_face_set P) (at level 40).

CoInductive pb_face_spec (P : {poly base}) : {poly base} -> Prop :=
| PbEmptyFace : pb_face_spec P ([poly0])%:poly_base
| PbArgMin c of (bounded P c) : pb_face_spec P (argmin P c)%:poly_base.

Lemma pb_faceP (P Q : {poly base}) :
  Q \in \face_set P -> pb_face_spec P Q.
Proof.
case: (emptyP ('P(base) : 'poly[R]_n))
  => [base_eq0 | base_prop0].
- suff ->: (P = ([poly0]%:poly_base)).
  + rewrite inE RT.lex0 => /eqP.
    move/val_inj ->; constructor.
    move: (poly_base_subset P); rewrite base_eq0 //=.
      by rewrite RT.lex0 => /eqP/val_inj.
- case: (poly_baseP Q) => [-> | ]; first constructor.
  move => I [Q_eq Q_prop0].
  rewrite inE; move => Q_sub_P.
  pose w : {conic lrel ~> R} := (fconicu I).
  pose c := (combine w).1.
  have c_bounded : bounded ('P(base) : 'poly[R]_n) c.
  + apply: dual_sol_bounded => //; rewrite finsupp_fconicu; exact: fsubset_subP.
  have c_bounded_P : (bounded P c).
  + apply: (bounded_mono1 c_bounded); apply/andP; split;
      [ exact: (RT.lt_le_trans Q_prop0) | exact: poly_base_subset ].
  have c_argmin: argmin 'P(base) c = Q.
  + rewrite Q_eq in Q_prop0 *.
    rewrite dual_sol_argmin /=; rewrite ?/w ?finsupp_fconicu //.
    exact: fsubset_subP.
  suff <- : (argmin P c)%:poly_base = Q by constructor.
  apply: val_inj => /=. rewrite -c_argmin.
  apply/subset_argmin; first by done.
  apply/andP; split; [ by rewrite c_argmin | exact: poly_base_subset ].
Qed.

Lemma argmin_pb_face_set (P : {poly base}) c:
  (argmin P c)%:poly_base \in \face_set P.
Proof.
by rewrite inE argmin_subset.
Qed.

End PolyBaseFace.

Notation "\face_set P" := (pb_face_set P) (at level 40).

Section Face.
Variable (R : realFieldType) (n : nat).

Definition face_set (P : 'poly[R]_n) :=
  [fset pval x | x in \face_set (\repr P)]%fset.

Lemma face_set_morph (base : base_t[R,n]) (P : {poly base}) :
  face_set P = [fset pval x | x in \face_set P]%fset.
Proof.
suff H: forall base1 base2 (P1 : {poly base1}) (P2 : {poly base2}),
    P1 = P2 :> 'poly[R]_n ->
    ([fset pval x | x in \face_set P1] `<=` [fset pval x | x in \face_set P2])%fset.
- by apply/eqP; rewrite eqEfsubset; apply/andP; split; apply/H; rewrite reprK.
- move => base1 base2 P1 P2 eq_P12.
  apply/fsubsetP => F /imfsetP [F' /= F'_in ->].
  case/pb_faceP : F'_in.
  + apply/imfsetP; exists ([poly0]%:poly_base) => //=.
    rewrite inE; exact: RT.le0x.
  + move => c c_bounded.
    apply/imfsetP; exists ((argmin P2 c)%:poly_base) => /=.
    rewrite inE; exact: argmin_subset.
    by rewrite eq_P12.
Qed.

Lemma face_has_base (base : base_t[R,n]) (P : {poly base}) (Q : 'poly[R]_n) :
  Q \in face_set P -> [Q has \base base].
Proof.
rewrite face_set_morph => /imfsetP [{}Q _ ->].
exact: pvalP.
Qed.

(*Canonical face_set_has_baseP (base : base_t[R,n]) (P : {poly base}) (Q : 'poly[R]_n) (H : expose (Q \in face_set P)) :=
  PolyBase (face_set_has_base H).*)

(*Parameter (base : base_t[R,n]) (P : {poly base}) (Q : 'poly[R]_n).
Hypothesis H : (Q \in face_set P).
Check (Q%:poly_base) : {poly base}.*)

Lemma face_setE (base : base_t[R,n]) (P : {poly base}) :
    (forall F : {poly base}, (pval F \in face_set P) = (pval F `<=` pval P))
    * (forall F : 'poly[R]_n, forall H : [F has \base base], (F \in face_set P) = (F `<=` pval P)).
Proof.
set X := (X in (X * _)%type).
suff hX: X.
- split => //.
  move => F F_base; have ->: F = PolyBase F_base by []; exact: hX.
- move => F; rewrite face_set_morph.
  apply/imfsetP/idP => [[{}F H /=->]| F_sub_P]; first by rewrite inE in H.
  by exists F; rewrite ?inE.
Qed.

Lemma face_self (P : 'poly[R]_n) : P \in (face_set P).
Proof.
elim/polybW: P => base P.
rewrite face_setE; exact: RT.lexx.
Qed.

Variant face_spec (base : base_t[R, n]) (P : {poly base}) : 'poly[R]_n -> Type :=
| FaceSetSpec (Q : {poly base}) of (pval Q `<=` pval P) : face_spec P Q.

Lemma faceP (base : base_t[R, n]) (P : {poly base}) (Q : 'poly[R]_n) :
  (Q \in face_set P) -> @face_spec base P Q.
Proof.
move => Q_face_P.
have Q_eq : Q = (PolyBase (face_has_base Q_face_P)) by [].
move: (Q_face_P); rewrite Q_eq => Q_face_P'.
constructor; by rewrite face_setE in Q_face_P'.
Qed.

Lemma face_closed (P : 'poly[R]_n) :
  [&& premeet_closed poly_preLattice (face_set P),
      premeet_closed [preLattice of dual_rel poly_subset] (face_set P) &
      face_set P != fset0].
Proof.
elim/polybW: P => base P.
apply/and3P; split; try do [apply/premeet_closedP=> F F';
  case/faceP=> {}F F_sub_P;
  case/faceP=> {}F' F'_sub_P; rewrite /= /Mmeet /Mjoin face_setE].
- by rewrite RT.leIxl.
- by apply/(RT.meet_max_seq (face_self P)) => //; apply/andP; split.
  set X := (X in [X has \base base]).
  have ->: X = \polyI_(i <- face_set P | (F `<=` i) && (F' `<=` i)) i by [].
  rewrite big_seq_cond
          (big_rem_idx (Q := predT) _ _ _ _ _ (face_self P)) ?RT.meetx1 => //.
  + elim/big_ind: _.
    * exact: pvalP.
    * move=> Q Q' Q_base Q'_base.
      have-> : Q `&` Q' = (PolyBase Q_base) `&` (PolyBase Q'_base) by [].
      exact: pvalP.
    * by move=> Q /and3P [/face_has_base].
  + move => ?? _ _; exact: RT.meetC.
  + move => ??? _ _ _; exact: RT.meetA.
  + by rewrite face_self /=; apply/andP; split.
- by apply/fset0Pn; exists [poly0]; rewrite face_setE RT.le0x.
Qed.

Canonical face_lattice P := FinLattice (face_closed P).

(*Lemma in_face_setP (base : base_t[R,n]) (F : 'poly[R]_n) (P : {poly base}) & (F \in face_set P) :
  F%:poly_base `<=` P.
Proof.
by rewrite -face_setE.
Qed.*)

Lemma poly0_face (P : 'poly[R]_n) : [poly0] \in face_lattice P.
Proof. elim/polybW: P => base P; by rewrite face_setE ?RT.le0x. Qed.

Lemma face_lattice_of_face (P Q : 'poly[R]_n) :
  Q \in face_lattice P ->
    face_lattice Q = [< [poly0]; Q >]_(face_lattice P).
Proof.
elim/polybW: P => base P.
case/faceP => {}Q Q_sub_P.
apply/finlattice_eqP => Q'; apply/idP/idP.
- case/faceP => {}Q' Q'_sub_Q.
  apply/mem_itv => //; rewrite ?face_setE; exact: (RT.le_trans Q'_sub_Q).
- case/intervalP; rewrite ?RT.le0x //.
  + exact: poly0_face.
  + by rewrite face_setE.
  + by case/faceP => {}Q' _; rewrite face_setE.
Qed.

Corollary faceS (P Q : 'poly[R]_n) :
  Q \in face_lattice P -> (face_lattice Q `<=` face_lattice P)%fset.
Proof.
move/face_lattice_of_face ->; apply/fsubsetP => Q'.
exact: itv_subset.
Qed.

Lemma face_subset (F : 'poly[R]_n) (P : 'poly[R]_n)  :
  F \in face_lattice P -> F `<=` P.
Proof. elim/polybW: P => base P; by case/faceP => ?. Qed.

Lemma face0 :
  face_lattice [poly0] = [finlattice [poly0] for poly_preLattice].
Proof.
apply/finlattice_eqP => P; rewrite !inE; apply/idP/idP.
- by move/face_subset; rewrite RT.lex0.
- move/eqP ->; exact: face_self.
Qed.

Lemma argmin_in_face_lattice (P : 'poly[R]_n) c :
  bounded P c -> argmin P c \in face_set P.
Proof.
elim/polybW: P => base P c_bounded.
by rewrite face_setE ?pvalP ?argmin_subset.
Qed.

Lemma face_argmin (P Q : 'poly[R]_n) :
  Q \in face_set P -> Q `>` ([poly0]) -> exists2 c, bounded P c & Q = argmin P c.
Proof.
rewrite /face_set; move/imfsetP => [{}Q /= Q_face ->].
by case: (pb_faceP Q_face) => [| c]; rewrite /= ?reprK ?RT.ltxx //; exists c.
Qed.

Lemma face_compact (P Q : 'poly[R]_n) :
  compact P -> Q \in face_lattice P -> compact Q.
Proof.
by move => ? /face_subset; apply/subset_compact.
Qed.

Lemma face_pointed (P Q : 'poly[R]_n) :
  pointed P -> Q \in face_lattice P -> pointed Q.
Proof.
move => P_pointed.
by move/face_subset/pointedS/(_ P_pointed).
Qed.

End Face.

(* DEPRECATED *
 *
(* -------------------------------------------------------------------- *)
Section FaceSetOrder.
Context (R : realFieldType) (n : nat) (P : 'poly[R]_n).

Definition face_set_porderMixin :=
  Eval hnf in [porderMixin of face_set P by <:].
Canonical face_set_porderType :=
  Eval hnf in POrderType ring_display (face_set P) face_set_porderMixin.
Canonical face_set_finPOrderType :=
  Eval hnf in [finPOrderType of face_set P].
End FaceSetOrder.

(* -------------------------------------------------------------------- *)
Section FacesSetOrderTheory.
Context (R : realFieldType) (n : nat) (P : 'poly[R]_n).

Lemma leEfaces (F1 F2 : face_set P) :
  (F1 <= F2) = (val F1 `<=` val F2).
Proof. by []. Qed.

Lemma ltEfaces (F1 F2 : face_set P) :
  (F1 < F2) = (val F1 `<` val F2).
Proof. by []. Qed.

Definition lteEfaces := (leEfaces, ltEfaces).
End FacesSetOrderTheory.

(* -------------------------------------------------------------------- *)
Import MeetBTFinMixin.Exports.

Section FacesLattice.
Context (R : realFieldType) (n : nat) (P : 'poly[R]_n).

Lemma poly0_fp : [poly0] \in face_set P.
Proof. by apply: poly0_face_set. Qed.

Lemma polyP_fp : P \in face_set P.
Proof. by apply: face_set_self. Qed.

Let fp0 := [`poly0_fp]%fset.
Let fp1 := [`polyP_fp]%fset.

Definition fpI (F1 F2 : face_set P) : face_set P :=
  [`face_set_polyI (valP F1) (valP F2)]%fset.

Lemma fpIC : commutative fpI.
Proof.
move=> F1 F2; apply: val_inj; rewrite !SubK.
by apply/poly_eqP=> x; rewrite !in_polyI andbC.
Qed.

Lemma fp_le_def (F1 F2 : face_set P) : (F1 <= F2) = (fpI F1 F2 == F1).
Proof. by rewrite leEfaces -val_eqE fpIC /=; apply/esym/eq_meetr. Qed.

Lemma fp_lt_def (F1 F2 : face_set P) : (F1 < F2) = (F2 != F1) && (F1 <= F2).
Proof. by rewrite !lteEfaces lt_neqAle eq_sym. Qed.

Lemma fpIA : associative fpI.
Proof.
move=> F1 F2 F3; apply: val_inj; rewrite !SubK.
by apply/poly_eqP=> x; rewrite !in_polyI andbA.
Qed.

Lemma fpII : idempotent fpI.
Proof.
move=> F; apply: val_inj; rewrite !SubK.
by apply/poly_eqP=> x; rewrite !in_polyI andbb.
Qed.

Lemma fp0I (F : face_set P) : fp0 <= F.
Proof. by apply: le0x. Qed.

Lemma fpI1 (F : face_set P) : F <= fp1.
Proof. by apply/face_subset/valP. Qed.

Definition polyFaces_latticeMixin :=
   MeetBTFinMixin fp_le_def fpIC fpIA fpII fp0I fpI1.

Canonical face_set_MeetSemilatticeType :=
  Eval hnf in MeetSemilatticeType (face_set P) polyFaces_latticeMixin.
Canonical face_set_BSemilatticeType :=
  Eval hnf in BSemilatticeType (face_set P) polyFaces_latticeMixin.
Canonical face_set_latticeType :=
  Eval hnf in LatticeType (face_set P) polyFaces_latticeMixin.
Canonical face_set_bLatticeType :=
  [bLatticeType of face_set P].
Canonical face_set_tbLatticeType :=
  Eval hnf in TBLatticeType (face_set P) polyFaces_latticeMixin.
Canonical face_set_finLatticeType :=
  Eval hnf in [finLatticeType of (face_set P)].
End FacesLattice.
*)

Section Active.

Context {R : realFieldType} {n : nat} {base : base_t[R,n]}.

Fact active_key : unit. by []. Qed.

Definition active (P : {poly base}) := (* TODO: fix broken notation *)
  locked_with active_key
    ((\big[@fsetU _/fset0]_(I : {fsubset base} | (pval P `<=` 'P^=(base; I))) I)%:fsub).

Notation "'{eq'  P }" := (active P) : poly_scope.

Lemma repr_active (P : {poly base}) :
  P `>` ([poly0]) -> P = ('P^=(base; {eq P}))%:poly_base.
Proof.
case/poly_baseP: (P) => [->|]; first by rewrite RT.ltxx.
move => I [P_eq _] Pprop0; apply: val_inj => /=.
suff ->: 'P^=(base; {eq P}) =
  \polyI_(I : {fsubset base} | val P `<=` 'P^=(base; I)) 'P^= (base; I) :> 'poly[R]_n.
- rewrite (rwP eqP) (RT.eq_le [leo:<=%P]); apply/andP; split.
  + by apply/RT.meetsP.
  + rewrite P_eq; apply/RT.meets_inf; exact: RT.lexx.
- rewrite polyEq_big_polyI /active; first by rewrite unlock_with.
  apply/pred0Pn; rewrite P_eq /=; exists I.
  exact: RT.lexx.
Qed.

Lemma activeP (P : {poly base}) (I : {fsubset base}) :
  (pval P `<=` 'P^=(base; I)) = (I `<=` {eq P})%fset.
Proof.
apply/idP/idP.
- by move => Psub; rewrite /active unlock_with; apply/bigfcup_sup.
- case: (emptyP P) => [/= -> _|]; first exact: RT.le0x.
  move/repr_active => {2}-> /=.
  exact: polyEq_antimono.
Qed.

Lemma subset_repr_active {P : {poly base}} :
  pval P `<=` 'P^=(base; {eq P}).
apply/poly_leP => x x_in_P.
have h: P `>` ([poly0]) by apply/proper0P; exists x.
by rewrite [P]repr_active in x_in_P.
Qed.

Lemma active0 :
  {eq ([poly0]%:poly_base : {poly base})} = base%:fsub.
Proof.
set A := {eq _}.
apply/val_inj/FSubset.untag_inj => /=.
apply/eqP; rewrite eqEfsubset; apply/andP; split; first exact: fsubset_subP.
- rewrite -activeP => /=; exact: RT.le0x.
Qed.

Lemma active_polyEq (I : {fsubset base}) :
  (I `<=` {eq 'P^=(base; I)%:poly_base})%fset.
Proof.
rewrite -activeP; exact: RT.lexx.
Qed.

Lemma poly_base_subset_hp {P : {poly base}} {e} :
  (e \in ({eq P} : {fset _})) -> (pval P `<=` [hp e]).
Proof.
move => h.
have e_in_base : ([fset e] `<=` base)%fset.
- rewrite fsub1set.
  by apply/(fsubsetP (fsubset_subP {eq P})).
set se := [fset e]%:fsub%fset : {fsubset base}.
have: (se `<=` {eq P})%fset by  rewrite fsub1set.
rewrite -activeP polyEq1 => P_sub.
by apply: (RT.le_trans P_sub); exact: RT.leIr.
Qed.

Lemma in_active {P : {poly base}} {e} :
  e \in base -> (e \in ({eq P} : {fset _})) = (pval P `<=` [hp e]).
Proof.
move => e_in_base.
apply/idP/idP; first exact: poly_base_subset_hp.
set se := [fset e]%:fsub%fset : {fsubset base}.
move => P_sub.
suff: (se `<=` {eq P})%fset by  rewrite fsub1set.
by rewrite -activeP polyEq1 RT.lexI poly_base_subset.
Qed.

Lemma activeS :
  {homo active : P Q / (pval P `<=` pval Q) >-> (val Q `<=` val P)%fset}.
Proof.
move => P Q; case: (poly_baseP P) => [-> | ? [_ P_prop0]].
- rewrite active0 RT.le0x => _; exact: fsubset_subP.
- case: (poly_baseP Q) => [-> | ? [_ Q_prop0]].
  + rewrite RT.lt0x -RT.lex0 in P_prop0.
    by move/negbTE : P_prop0 ->.
  move/repr_active: Q_prop0 => {1}->.
  by rewrite activeP.
Qed.

Lemma activeI (P Q : {poly base}) :
  ({eq P} `|` {eq Q} `<=` {eq ((pval P `&` pval Q)%PH)%:poly_base})%fset.
Proof. by rewrite -activeP -polyEq_polyI RT.leI2 ?activeP. Qed.

Lemma poly_base_proper (P Q : {poly base}) :
  ({eq Q} `<` {eq P})%fset -> pval P `<` pval Q.
Proof.
case: (poly_baseP Q) => [->| J [Q_eq Q_prop0]]; first by rewrite active0 fsubsetT_proper.
case: (poly_baseP P) => [->| I [P_eq P_prop0]]; first by [].
rewrite {2}[Q]repr_active // => /fproperP [/fsubsetP eq_sub] [i i_in i_notin].
rewrite [P]repr_active //.
apply/andP; split; last exact: polyEq_antimono.
rewrite (RT.eq_le [leo:<=%P]) /= polyEq_antimono //=.
apply/poly_lePn.
move: i_notin; rewrite in_active.
- move/poly_lePn => [x x_in_Q x_notin].
  exists x; first by move/(poly_leP subset_repr_active): x_in_Q.
  move: x_notin; apply: contra => x_in; exact: (polyEq_eq x_in).
- move: i_in; apply/fsubsetP; exact: fsubset_subP.
Qed.

Lemma active_proper (P Q : {poly base}) :
  [poly0] `<` P -> val P `<` Q -> ({eq Q} `<` {eq P})%fset.
Proof.
move => P_prop0 P_prop_Q; rewrite fproperEneq.
have Q_prop0: Q `>` [poly0] by apply/RT.lt_trans: P_prop_Q.
move/RT.ltW/activeS: (P_prop_Q) ->.
rewrite andbT; move: P_prop_Q; apply: contraTneq.
rewrite {2}[P]repr_active // {2}[Q]repr_active // /val_inj /= => ->.
by rewrite RT.ltxx.
Qed.

Lemma active_affine :
  {eq (affine <<base>>)%:poly_base} = base%:fsub.
Proof.
apply/fsubset_inj/eqP; rewrite eqEfsubset.
rewrite fsubset_subP //=.
apply/fsubsetP => i ?; rewrite in_active //=.
by apply/affineS1/memv_span.
Qed.

End Active.

Notation "'{eq'  P }" := (active P) : poly_scope.

Section ActiveSlice.

Variable (R : realFieldType) (n : nat).

Lemma active_slice e (base : base_t[R,n]) (P : {poly base}) :
  ((e +|` {eq P}) `<=` {eq (slice e P)%:poly_base})%fset.
Proof.
rewrite -activeP -slice_polyEq.
case: (poly_baseP P) => [-> /= | ? [_ P_prop0] /=].
- rewrite {1}(slice0 _); exact: RT.le0x.
- move/repr_active: P_prop0 => {1}->.
  exact: RT.le_trans.
Qed.

End ActiveSlice.

Section SpanActive.

Context {R : realFieldType} {n : nat}.

Implicit Types (base : base_t[R,n]).

Lemma in_span_active base (P : {poly base}) e :
  (e \in << {eq P} >>%VS) -> (pval P `<=` [hp e]).
Proof.
move/coord_span ->.
apply/poly_leP => x x_in_P; rewrite inE; apply/eqP.
rewrite (big_morph (id1 := 0) (op1 := +%R) (fun x : lrel[R]_n => x.1)) //.
rewrite (big_morph (id1 := 0) (op1 := +%R) (fun x : lrel[R]_n => x.2)) //=.
rewrite vdot_sumDl; under eq_big do [| rewrite /= vdotZl].
apply/eq_bigr => i _; apply: congr1.
apply/eqP; rewrite -in_hp; move: x_in_P; apply/poly_leP/poly_base_subset_hp.
by rewrite mem_nth ?size_tuple.
Qed.

Lemma in_span_activeP base (P : {poly base}) e :
  (P `>` [poly0]) ->
  (pval P `<=` [hp e]) = (e \in << {eq P} >>%VS).
Proof.
move => P_prop0; apply/idP/idP; last exact : in_span_active.
move: (erefl P); rewrite {2}[P]repr_active // => /(congr1 (@pval _ _ _)) /=.
rewrite polyEq_flatten => P_eq P_sub_hp.
move: (RT.le_trans P_sub_hp (hp_subset_hs _)).
move: (P_prop0); rewrite P_eq; set S := {eq P}: {fset _}.
move/farkas => h /h {h} [w w_supp [e1_eq e2_le]].
suff finsupp_sub_eq: (finsupp w `<=` (S `|` -%R @` S))%fset.
- have comb_in_eqP: combine w \in << {eq P} >>%VS.
  * rewrite (combinewE finsupp_sub_eq).
    apply/memv_suml => i _; rewrite memvZ //.
    move: (valP i); rewrite inE; move/orP; case; try exact: memv_span.
      by move/imfsetP => [? /= ? ->]; rewrite memvN memv_span.
  suff <-: (combine w) = e by [].
  move/proper0P: P_prop0 => [x x_in_P].
  apply/(befst_inj (x := x)) => //.
  * by apply/poly_leP/in_span_active: x_in_P.
  * by move/poly_leP/(_ _ x_in_P): P_sub_hp.
- move: P_sub_hp; apply: contraTT.
  move/fsubsetPn => [e']; rewrite inE negb_or => e'_in /andP [e'_notin_S /negbTE e'_notin_mS].
  have {e'_notin_S e'_notin_mS} /poly_lePn [x x_in x_notin]: ~~ (val P `<=` [hp e']).
  + rewrite -in_active ?e'_notin_S //.
    by move/fsubsetP/(_ _ e'_in): w_supp; rewrite inE e'_notin_mS orbF.
  apply/poly_lePn; exists x => //.
  rewrite in_hp -e1_eq eq_sym; apply/ltr_neq.
  apply/(le_lt_trans e2_le);
  rewrite !(combinebE w_supp) /= vdot_sumDl.
  apply/sumr_ltrP.
  + move => i; rewrite vdotZl ler_wpmul2l ?ge0_fconic //.
    rewrite -in_hs; move: x_in; apply/poly_leP => /=.
    rewrite P_eq; apply/poly_base_subset_hs; exact: fsvalP.
  + have e'_in_baseEq : e' \in baseEq base S by apply/(fsubsetP w_supp).
    pose e'_idx := [` e'_in_baseEq]%fset.
    exists e'_idx. rewrite vdotZl ltr_pmul2l ?gt0_fconic //.
    rewrite -notin_hp //=.
    move: x_in; apply/poly_leP => /=.
    by rewrite P_eq; apply/poly_base_subset_hs.
Qed.

Lemma span_activeS base (P : {poly base}) base' (Q : {poly base'}) :
  (P `>` [poly0]) -> pval P `<=` pval Q -> (<< {eq Q} >> <= << {eq P} >>)%VS.
Proof.
move => P_prop0 P_sub_Q; apply/subvP => e /in_span_active.
rewrite -in_span_activeP //; exact: RT.le_trans.
Qed.

Lemma span_activeE base (P : {poly base}) base' (Q : {poly base'}) :
  (P `>` [poly0]) -> P = Q :> 'poly[R]_n -> (<< {eq P} >> = << {eq Q} >>)%VS.
Proof.
move => P_prop0 P_eq_Q.
by apply/subv_anti; apply/andP; split; apply/span_activeS; rewrite -?P_eq_Q ?poly_subset_refl.
Qed.

End SpanActive.

Section AffineHull.

Context {R : realFieldType} {n : nat}.

Implicit Type base : base_t[R,n].

Definition pb_hull base (P : {poly base}) :=
  if P `>` [poly0] then
    affine << {eq P} >>%VS
  else
    [poly0].

Notation "\hull P" := (pb_hull P) (at level 40).

Definition hull (P : 'poly[R]_n) := \hull \repr P.

Lemma hullE base (P : {poly base}) :
  hull P = \hull P.
Proof.
case: (emptyP P)  => [| P_propØ].
- rewrite /hull /pb_hull => ->.
  by rewrite ifF ?reprK ?RT.ltxx.
- rewrite /hull /pb_hull reprK !ifT //=.
  suff ->: (<<{eq P}>> = <<{eq \repr P}>>)%VS by [].
  by apply/span_activeE; rewrite ?reprK.
Qed.

Lemma subset_hull P : P `<=` hull P.
Proof.
case: (emptyP P) => [->| ]; rewrite ?le0x //.
elim/polybW : P => base P; rewrite hullE /pb_hull => P_prop0.
by rewrite P_prop0; rewrite {1}[P]repr_active //= polyEq_affine RT.leIr.
Qed.

Lemma hull0 : hull ([poly0] : 'poly[R]_n) = [poly0].
by rewrite /hull /pb_hull reprK ifF ?poly_properxx.
Qed.

Lemma hullN0 P : (P `>` [poly0]) = (hull P `>` [poly0]).
Proof.
case/emptyP : (P) => [-> | P_prop0]; first by rewrite hull0 RT.ltxx.
by symmetry; apply/(RT.lt_le_trans P_prop0)/subset_hull.
Qed.

Lemma hullN0_eq base (P : {poly base}) :
  (P `>` [poly0]) -> hull P = affine << {eq P} >>.
Proof.
by rewrite hullE /pb_hull => ->.
Qed.

Lemma hullP P U :
  (P `<=` affine U) = (hull P `<=` affine U).
Proof.
case: (emptyP P) => [->|]; rewrite ?hull0 //.
move => P_prop0; apply/idP/idP; last by apply/RT.le_trans; exact: subset_hull.
elim/polybW : P P_prop0 => base P P_prop0.
rewrite hullN0_eq // => P_sub_affU; apply: affineS.
apply/subvP => e; rewrite -in_span_activeP //.
by move/affineS1; apply/RT.le_trans.
Qed.

Lemma hull_affine U :
  hull (affine U) = affine U.
Proof.
by apply/eqP; rewrite (RT.eq_le [leo:<=%P]); rewrite ?subset_hull -?hullP RT.lexx.
Qed.

Lemma hullI (P : 'poly[R]_n) : hull (hull P) = hull P.
Proof.
case: (emptyP P) => [->|]; first by rewrite !hull0.
elim/polybW: P => base P P_prop0.
by rewrite hullN0_eq // hull_affine.
Qed.

Lemma hullS : {homo hull : P Q / P `<=` Q}.
Proof.
move => P Q.
case: (emptyP Q) => [->|];
  first by rewrite RT.lex0 => /eqP ->; exact: RT.lexx.
elim/polybW : Q => base Q Q_prop0 P_sub_Q.
rewrite hullN0_eq // hullP hullI -hullP.
rewrite -hullN0_eq //; apply/(RT.le_trans P_sub_Q); exact: subset_hull.
Qed.

Lemma line_subset_hull (P : 'poly[R]_n) (v v' : 'cV[R]_n) :
  v \in P -> v' \in P -> [line (v' - v) & v] `<=` hull P.
Proof.
elim/polybW: P => base P v_in_P v'_in_P.
have P_prop0: P `>` [poly0] by apply/proper0P; exists v.
rewrite hullN0_eq // affine_span; apply/RT.meetsP => e _.
by apply/line_subset_hp; apply/(poly_leP (poly_base_subset_hp (valP _))).
Qed.

Lemma hull_line (v v' : 'cV[R]_n) :
  hull [segm v & v'] = [line (v' - v) & v].
Proof.
set S := conv _; rewrite (rwP eqP) (RT.eq_le [leo: <=%P]); apply/andP; split; last first.
- by apply/line_subset_hull; [rewrite in_segml | rewrite in_segmr].
have eq := line_affine v (v' - v); rewrite /mk_affine in eq.
rewrite eq -hullP -eq. (* TODO: we shouldn't have to use /mk_affine *)
apply/conv_subset => x; rewrite !inE => /orP; case => /eqP ->; apply/in_lineP.
- by exists 0; rewrite scale0r addr0.
- by exists 1; rewrite scale1r addrCA addrN addr0.
Qed.

Lemma hull_pt (v : 'cV[R]_n) : hull [pt v] = [pt v].
Proof.
have {1}->: [pt v] = [segm v & v].
+ apply/poly_eqP => x; rewrite in_pt; apply/eqP/idP.
  * by move=> ->; rewrite in_segml.
  by case/in_segmP=> u rgu; rewrite -scalerDl subrK scale1r.
by rewrite hull_line subrr line0.
Qed.

Lemma face_hullI (P Q : 'poly[R]_n) :
  Q \in face_lattice P -> Q = P `&` hull Q.
Proof.
elim/polybW : P => base P.
case/faceP => {}Q Q_sub_P.
case: (emptyP Q) => [->| Q_prop0]; first by rewrite hull0 RT.meetx0.
rewrite hullN0_eq //.
rewrite [Q in LHS]repr_active //= polyEq_affine.
rewrite [P]repr_active /= ?polyEq_affine -?polyIA.
move: (Q_sub_P) => /activeS/fsubsetP/sub_span/affineS/RT.meet_r.
by rewrite -RT.meetA => ->.
by apply/RT.lt_le_trans: Q_sub_P.
Qed.

End AffineHull.

Section Dimension.

Variable (R : realFieldType) (n : nat).

Definition pb_dim (base : base_t[R,n]) (P : {poly base}) :=
  if (P `>` [poly0]) then
    (n - \dim << {eq P} >>).+1%N
  else 0%N.

Notation "\dim P" := (pb_dim P) (at level 10, P at level 8) : poly_scope.

Definition dim (P : 'poly[R]_n) := \dim (\repr P).

Lemma dimE (base : base_t[R,n]) (P : {poly base}) :
  dim P = \dim P.
Proof.
case: (emptyP P) => [| P_propØ].
- rewrite /dim /pb_dim => ->.
  by rewrite ifF ?reprK ?RT.ltxx.
- rewrite /dim /pb_dim reprK !ifT //.
  by do 3![apply/congr1]; symmetry; apply/span_activeE; rewrite ?reprK.
Qed.

Lemma dim_le_Sn (P : 'poly[R]_n) :
  (dim P <= n.+1)%N.
Proof.
elim/polybW: P => base P; rewrite dimE /pb_dim.
by case: ifP => [_|//]; apply: leq_subr.
Qed.

Lemma dim0 :
  (dim ([poly0] : 'poly[R]_n) = 0%N)
  * (forall base, dim ([poly0] %:poly_base : {poly base}) = 0%N).
Proof.
suff H : forall base, dim ([poly0] %:poly_base : {poly base}) = 0%N.
- split => //.
  pose base0 := fset0 : base_t[R,n].
  by rewrite H.
- by move => base; rewrite dimE /pb_dim ifF // poly_properxx.
Qed.

Lemma dimN0 (P : 'poly[R]_n) : (P `>` [poly0]) = (dim P > 0)%N.
Proof.
case/emptyP : (P) => [-> | P_prop0]; first by rewrite dim0 ltnn.
by elim/polybW: P P_prop0 => base P P_prop0; rewrite dimE /pb_dim ifT.
Qed.

Lemma dimN0_eq (base : base_t[R,n]) (P : {poly base}) :
  (P `>` [poly0]) -> dim P = (n - \dim << {eq P} >>).+1%N.
Proof.
by rewrite dimE /pb_dim => ->.
Qed.

Lemma dim_eq0 (P : 'poly[R]_n) :
  dim P = 0%N <-> P = [poly0].
Proof.
split; last by move ->; rewrite dim0.
by apply/contra_eq; rewrite -RT.lt0x dimN0 lt0n.
Qed.

Lemma dim_affine (U : {vspace 'cV[R]_n}) Ω :
  (dim [affine U & Ω] = (\dim U).+1)%N.
Proof.
move: (mk_affine_prop0 U Ω).
rewrite /mk_affine.
set V := (X in affine X).
set base := [fset e in ((vbasis V) : seq _)]%fset : {fset lrel[R]_n}.
have eq: V = << base >>%VS.
- move: (vbasisP V) => /andP [/eqP <- _].
  apply/subv_anti/andP; split; apply/sub_span;
  by move => ?; rewrite inE.
rewrite eq => prop0; rewrite dimN0_eq ?active_affine //=.
by rewrite -eq dim_mk_affine_fun dim_orthv subKn ?dim_cVn.
Qed.

Variant dim_spec : 'poly[R]_n -> nat -> Prop :=
| DimEmpty : dim_spec ([poly0]) 0%N
| DimNonEmpty (base : base_t[R,n]) (P : {poly base}) of (P `>` [poly0]) : dim_spec P (n-\dim <<{eq P}>>).+1.

Lemma dimP P : dim_spec P (dim P).
case: (emptyP P) => [->| ]; first by rewrite dim0; constructor.
by elim/polybW: P => base P P_prop0; rewrite dimN0_eq //; constructor.
Qed.

Lemma dim_hull (P : 'poly[R]_n) :
  dim P = dim (hull P).
Proof.
case/dimP: P => [| base P P_prop0]; first by rewrite hull0 dim0.
have hull_prop0: (hull P) `>` [poly0] by apply/(RT.lt_le_trans P_prop0); exact: subset_hull.
rewrite hullN0_eq // in hull_prop0 *.
by rewrite dimN0_eq //= active_affine.
Qed.

Lemma dimS : {homo dim : P Q / (P `<=` Q) >-> (P <= Q)%N}.
Proof.
move => P Q.
case/dimP: P => [| base P P_prop0]; rewrite ?dim0 //.
case/dimP: Q => [| base' Q Q_prop0];
  first by move/(RT.lt_le_trans P_prop0); rewrite ?RT.ltxx.
by rewrite ltnS => P_sub_Q; apply/leq_sub2l/dimvS/span_activeS.
Qed.

Lemma hull_mk_affine {P : 'poly[R]_n} {x} :
  x \in P -> exists2 U, hull P = [affine U & x] & (\dim U = (dim P).-1)%N.
Proof.
elim/polybW: P => base P x_in_P.
have P_prop0 : P `>` [poly0] by apply/proper0P; exists x.
set U := (befst @: <<{eq P}>>)^OC%VS.
have hullP : hull P = [affine U & x].
- by rewrite -affine_orth -hullN0_eq //; apply/(poly_leP (subset_hull _)).
exists U => //; by rewrite dim_hull hullP dim_affine /=.
Qed.

Lemma dim_affine_lt (U V : {vspace lrel}) :
  affine U `<` affine V -> (dim (affine U) < dim (affine V))%N.
Proof.
case: (emptyP (affine U)) => [->|/proper0P [x x_in_U]]; first by rewrite dim0 dimN0.
move => U_prop_V; have U_sub_V := (RT.ltW U_prop_V).
have x_in_V : x \in affine V by apply/(poly_leP U_sub_V): x_in_U.
move: U_prop_V; rewrite RT.lt_neqAle andbC U_sub_V /=.
apply/contra_neqT; rewrite (affine_orth x_in_U) (affine_orth x_in_V) in U_sub_V *.
rewrite mk_affineS in U_sub_V.
rewrite 2!dim_affine -leqNgt ltnS => dim_le.
by apply/(congr1 ((fun y => mk_affine y x)))/eqP; rewrite eqEdim U_sub_V.
Qed.

Lemma dim_span_active (base : base_t[R,n]) (P : {poly base}) :
  P `>` ([poly0]) -> (\dim << {eq P} >> <= n)%N.
Proof.
move => /proper0P [x x_in_P].
have /limg_dim_eq <-: (<<{eq P}>> :&: lker befst)%VS = 0%VS.
- apply/eqP; rewrite -subv0.
  apply/subvP => e; rewrite memv_cap memv_ker memv0 => /andP [e_in /eqP f_e_eq0].
  have e1_eq0 : e.1 = 0 by rewrite lfunE in f_e_eq0.
  apply/be_eqP => /=; split; first done.
  move/(poly_leP subset_repr_active): x_in_P.
  rewrite polyEq_affine in_polyI => /andP [_ /in_affine/(_ _ e_in)].
  by rewrite in_hp e1_eq0 vdot0l => /eqP.
- apply/(leq_trans (n := \dim fullv)); first by apply/dimvS/subvf.
  by rewrite dimvf /Vector.dim /= muln1.
Qed.

Lemma face_dim_leqif_eq (P Q : 'poly[R]_n) :
  (P \in face_lattice Q) -> (dim P <= dim Q ?= iff (P == Q))%N.
Proof.
move => P_face_Q; split; first by apply/dimS; exact: face_subset.
apply/eqP/eqP => [| -> //].
case/dimP: Q P_face_Q => [_ /dim_eq0 //| base Q Q_prop0].
case/faceP => {}P P_sub_Q.
case: (emptyP P) => [->| P_prop0]; rewrite ?dim0 //.
rewrite dimN0_eq // => /eqP; rewrite eqSS subn_inj ?dim_span_active // => /eqP dim_eq.
suff: (<< {eq P} >> = << {eq Q} >>)%VS.
- by rewrite {2}[P]repr_active ?{2}[Q]repr_active //= ?polyEq_affine => ->.
- apply/eqP; rewrite eq_sym eqEdim {}dim_eq leqnn andbT.
  by apply/span_activeS.
Qed.

Lemma face_dim_geq (P Q : 'poly[R]_n) :
  P \in face_lattice Q -> (dim P >= dim Q)%N -> P = Q.
Proof.
move/face_dim_leqif_eq/geq_leqif => h dim_geq.
by rewrite dim_geq in h; move/esym/eqP: h.
Qed.

Lemma face_dim_eq (P Q : 'poly[R]_n) :
  P \in face_lattice Q -> dim P = dim Q -> P = Q.
Proof.
by move => ? dim_eq; apply/face_dim_geq; rewrite ?dim_eq.
Qed.

Lemma face_dim_lt (P Q Q' : 'poly[R]_n) :
  Q \in face_lattice P -> Q' \in face_lattice P -> Q `<` Q' -> (dim Q < dim Q')%N.
Proof.
move => Q_face Q'_face Q_prop_Q'.
have {Q_face Q'_face} Q_face_Q': Q \in face_lattice Q'
  by rewrite (face_lattice_of_face Q'_face) mem_itv // RT.ltW.
move: Q_prop_Q'; apply/contraTT.
rewrite -leqNgt => /(face_dim_geq Q_face_Q') ->.
by rewrite RT.ltxx.
Qed.

Lemma dim_pt (x : 'cV[R]_n) :
  dim [pt x] = 1%N.
Proof.
by rewrite dim_affine dimv0.
Qed.

Lemma dim1P (P : 'poly[R]_n) :
  reflect (exists x, P = [pt x]) (dim P == 1%N).
Proof.
apply/(iffP eqP) => [ dim1| [? ->]]; last exact: dim_pt.
have P_prop0: (P `>` [poly0]) by rewrite dimN0 dim1.
move/proper0P: (P_prop0) => [x x_in_P].
exists x; apply/(RT.le_anti [leo: <=%P]); apply/andP; split; last first.
- by rewrite pt_subset.
elim/polybW : P P_prop0 x_in_P dim1 => base P P_prop0.
move/(poly_leP (subset_hull _)) => x_in_hullP dim1.
apply/(RT.le_trans (subset_hull _)).
rewrite !hullN0_eq // in x_in_hullP *.
apply/poly_leP => y.
move: dim1; rewrite dim_hull hullN0_eq //.
by rewrite (affine_orth x_in_hullP) dim_affine => /succn_inj/eqP; rewrite dimv_eq0 => /eqP ->.
Qed.

Lemma dim_line (Ω d : 'cV[R]_n) :
  dim [line d & Ω] = (d != 0%R).+1.
Proof.
case/altP: (d =P 0) => [->|]; first by rewrite /= line0 dim_pt.
by rewrite line_affine dim_affine dim_vline => ->.
Qed.

Lemma dim_segm (v v' : 'cV[R]_n) : dim [segm v & v'] = (v != v').+1.
Proof.
by rewrite dim_hull hull_line dim_line subr_eq0 eq_sym.
Qed.

Lemma dim2P (P : 'poly[R]_n) :
  compact P -> dim P = 2 -> exists v, exists2 w, P = [segm v & w] & v != w.
Proof.
elim/polybW: P => base P P_compact dimP2.
have P_prop0 : P `>` [poly0] by rewrite dimN0 dimP2.
set U := (befst @: <<{eq P}>>)^OC%VS.
have hullP_eq : forall x, x \in P -> hull P = [affine U & x].
- move => x x_in_P.
  by rewrite -affine_orth -hullN0_eq //; apply/(poly_leP (subset_hull _)).
pose Ω := ppick P.
have dimU1 : (\dim U = 1)%N.
- by move: dimP2; rewrite dim_hull (hullP_eq _ (ppickP _)) // dim_affine => /succn_inj.
pose d := vpick U.
have d_neq0 : d != 0 by rewrite vpick0 -dimv_eq0 dimU1.
have d_bounded : bounded P d by apply/(compactP P_prop0).
have d_bounded' : bounded P (-d) by apply/(compactP P_prop0).
set v := ppick (argmin P d); set w := ppick (argmin P (-d)).
have v_in_argmin: v \in (argmin P d) by apply/ppickP; rewrite -bounded_argminN0.
have w_in_argmin: w \in (argmin P (-d)) by apply/ppickP; rewrite -bounded_argminN0.
have d_v : '[d,v] = opt_value d_bounded.
- by move: v_in_argmin; rewrite argmin_polyI in_polyI => /andP [_]; rewrite in_hp => /eqP.
have d_w : '[d,w] = -(opt_value d_bounded').
- move: w_in_argmin; rewrite argmin_polyI in_polyI => /andP [_]; rewrite in_hp => /eqP /=.
  by rewrite vdotNl => <-; rewrite opprK.
have v_in_P : v \in P by move: v_in_argmin; apply/(poly_leP (argmin_subset _ _)).
have w_in_P : w \in P by move: w_in_argmin; apply/(poly_leP (argmin_subset _ _)).
have dv_neq_dw: '[d,v] != '[d,w].
- move: d_neq0; apply: contra_neq => dv_eq_dw.
  pose e := [< d, opt_value d_bounded >].
  have: pval P `<=` [hp e].
  + rewrite RT.lexI -(rwP andP); split; first by apply/opt_value_lower_bound.
    rewrite beoppE /= -d_v dv_eq_dw d_w opprK.
    by apply/opt_value_lower_bound.
  rewrite in_span_activeP // => /(memv_img befst).
  rewrite lfunE /= => d_in_eq.
  have: d \in (U :&: U^OC)%VS by rewrite memv_cap orthK d_in_eq (memv_pick U).
  by rewrite direct_orthvP memv0 => /eqP.
have v_neq_w : v != w by move: dv_neq_dw; apply/contra_neq => ->.
have dv_lt_dw: '[d,v] < '[d,w].
- rewrite lt_neqAle dv_neq_dw /=.
  move/poly_leP/(_ _ w_in_P): (opt_value_lower_bound d_bounded).
  by rewrite in_hs -d_v /=.
exists v; exists w => //.
have U_eq: U = <[w-v]>%VS.
- apply/eqP; rewrite eq_sym eqEdim; apply/andP; split; last first.
  + by rewrite dimU1 dim_vline subr_eq0 eq_sym v_neq_w.
  + rewrite -memvE -in_mk_affine -(hullP_eq _ v_in_P).
    by apply/(poly_leP (subset_hull _)).
have {}hullP_eq : hull P = [line (w-v) & v].
- by rewrite line_affine -U_eq -hullP_eq.
apply/(RT.le_anti [leo: <=%P]); apply/andP; split; last first.
- by apply/conv_subset => x /fset2P; case => ->.
- apply/poly_leP => x x_in_P.
  move/(poly_leP (subset_hull _)): (x_in_P).
  rewrite hullP_eq => /in_lineP [μ x_eq].
  apply/in_segmP; exists μ; last first.
  + rewrite scalerDl scale1r addrAC scaleNr -scalerN.
    by rewrite x_eq scalerDr addrA.
  + apply/andP; split.
    * move/poly_leP/(_ _ x_in_P): (opt_value_lower_bound d_bounded).
      rewrite inE /= -d_v x_eq vdotDr vdotZr vdotBr ler_addl.
      by rewrite pmulr_lge0 ?subr_gt0.
    * move/poly_leP/(_ _ x_in_P): (opt_value_lower_bound d_bounded').
      rewrite inE /= vdotNl ler_oppr -d_w x_eq vdotDr vdotZr vdotBr addrC.
      by rewrite -ler_subr_addr ger_pmull ?subr_gt0.
Qed.

Lemma dim_hp (e : lrel[R]_n) :
  [hp e] `>` [poly0] -> dim [hp e] = ((e.1 == 0%R) + n)%N.
Proof.
move/proper0P => [x].
rewrite -affine1 => /affine_orth ->.
rewrite dim_affine dim_orthv limg_line lfunE /= dim_vline.
case/altP: (e.1 =P 0) => /= [_| e1_neq0].
- by rewrite subn0.
- rewrite subn1 add0n prednK //.
  move: e1_neq0; apply/contra_neqT; rewrite -eqn0Ngt => /eqP n_eq0.
  apply/colP => i; move: (valP i) => /=.
  by rewrite {2}n_eq0 ltn0.
Qed.

End Dimension.

Notation "\dim P" := (pb_dim P) (at level 10, P at level 8) : poly_scope.

Section Facet.

Context {R : realFieldType} {n : nat} (base : base_t[R,n]).
Hypothesis non_redundant : non_redundant_base base.

Let P := 'P(base)%:poly_base.
Hypothesis P_prop0 : P `>` [poly0].

Lemma activeU1 (e : lrel) & (e \in base) :
  {eq 'P^=(base; [fset e])%:poly_base } = ({eq P} `|` [fset e])%fset%:fsub.
Proof.
case: (boolP (e \in ({eq P} : base_t))).
- move => e_in_eqP.
  have ->: 'P^= (base; [fset e])%:poly_base = 'P(base)%:poly_base.
  + apply/val_inj => /=; rewrite polyEq1; apply/RT.meet_l.
    by apply/poly_base_subset_hp.
  apply/fsubset_inj => /=.
  by move: e_in_eqP; rewrite -fsub1set => /fsetUidPl ->.
- set I := ({eq P} `|` [fset e])%fset %:fsub.
  move => e_notin_eq; apply/fsubset_inj/eqP; rewrite eqEfsubset.
  apply/andP; split; last first.
  + apply/fsubUsetP; split; last exact: active_polyEq.
    apply/activeS => /=; exact: polyEq_antimono0.
  + apply/fsubset_fsubsetP => i i_in_eq; apply: contraLR.
    rewrite 2!inE negb_or => /andP [i_notin_eqP i_neq_e].
    apply/(contra poly_base_subset_hp)/poly_lePn.
    move/non_redundant_baseP/(_ _ H)/poly_lePn: non_redundant => [z z_in_P' z_notin_e].
    move: i_notin_eqP; rewrite in_active //.
    move/poly_lePn => [y y_in_P y_notin_i].
    have y_in_e : y \in [hs e] by apply/(poly_leP _ _ y_in_P)/poly_of_base_subset_hs.
    move: (hp_itv y_in_e z_notin_e) => [α α01]; rewrite {y_in_e}.
    set x := _ + _ => x_in_e; exists x.
    * rewrite /= polyEq1 inE x_in_e andbT.
      apply/in_poly_of_baseP => j.
      case: (j =P e) => [-> _| /eqP j_neq_e j_in_base].
      - move: x x_in_e; apply/poly_leP; exact: hp_subset_hs.
      - have y_in_P' : y \in 'P(base `\ e)
          by move: y_in_P; apply/poly_leP/poly_of_base_antimono; exact: fsubD1set.
        have: x \in 'P(base `\ e) by apply/mem_poly_convex => //; exact: ltW_le.
        apply/poly_leP/poly_of_base_subset_hs.
        by rewrite !inE j_neq_e.
    * move: y_notin_i; apply/contraNN/hp_extremeL => //.
      - by move: y_in_P; apply/poly_leP/poly_of_base_subset_hs.
      - move: z_in_P'; apply/poly_leP/poly_of_base_subset_hs.
        by rewrite !inE i_neq_e.
Qed.

Lemma facet_proper (i : lrel) & (i \in base) :
  i \notin ({eq P} : {fset _}) -> pval 'P^=(base; [fset i])%:poly_base `<` P.
Proof.
move => i_notin_eqP.
rewrite RT.lt_neqAle andbC; apply/andP; split.
- by rewrite /= -polyEq0; apply: polyEq_antimono.
- move: i_notin_eqP; apply: contraNneq => /pval_inj <-.
  rewrite -fsub1set; exact: active_polyEq.
Qed.

Lemma facet_proper0 (i : lrel) & (i \in base) : (* A LOT IN COMMON WITH activeU1 *)
  i \notin ({eq P} : {fset _}) -> 'P^=(base; [fset i])%:poly_base `>` [poly0].
Proof.
move => i_notin_eqP.
move/non_redundant_baseP/(_ _ H)/poly_lePn: non_redundant => [y y_in_P' y_notin_i].
move/proper0P: (P_prop0) => [x x_in_P].
have x_in_i : x \in [hs i] by move: x_in_P; apply/poly_leP/poly_of_base_subset_hs.
move: (hp_itv x_in_i y_notin_i) => [α α01].
set z := _ + _ => z_in_i; apply/proper0P; exists z.
rewrite /= polyEq1 inE z_in_i andbT.
apply/in_poly_of_baseP => j.
case: (j =P i) => [-> _| /eqP j_neq_i j_in_base].
- move: z z_in_i; apply/poly_leP; exact: hp_subset_hs.
- have x_in_P' : x \in 'P(base `\ i)
    by move: x_in_P; apply/poly_leP/poly_of_base_antimono; exact: fsubD1set.
  have: z \in 'P(base `\ i) by apply/mem_poly_convex => //; exact: ltW_le.
  by apply/poly_leP/poly_of_base_subset_hs; rewrite !inE j_neq_i.
Qed.

Lemma dim_facet (i : lrel) & (i \in base) :
  i \notin ({eq P} : {fset _}) -> dim P = (dim 'P^=(base; [fset i])%:poly_base).+1%N.
Proof.
set S := 'P^=(_; _)%:poly_base.
move => i_notin_eqP.
move/(facet_proper H): (i_notin_eqP) => S_prop_P.
have i_not_in_affP: i \notin << {eq P} >>%VS.
- move: S_prop_P; apply/contraTN; move/in_span_active.
  by rewrite /= polyEq1 => /RT.meet_l ->; rewrite RT.ltxx.
rewrite !dimN0_eq ?facet_proper0 //; apply: congr1.
rewrite activeU1 span_fsetU span_fset1 ?dim_add_line ?subnSK //=.
suff: (dim P > 1)%N by rewrite dimN0_eq // ltnS subn_gt0.
move/RT.ltW: (S_prop_P).
rewrite -face_setE => /face_dim_lt/(_ (face_self _))/(_ S_prop_P).
by apply/leq_ltn_trans; rewrite -dimN0 facet_proper0.
Qed.

Lemma facetP (F : {poly base}) :
  (F `>` [poly0]) -> dim P = (dim F).+1%N ->
  exists i, exists2 h : (i \in base), i \notin ({eq P} : {fset _}) & F = 'P^=(base; [fset i])%:poly_base.
Proof.
move => F_prop0 dimF.
suff: ~~ ({eq F} `<=` {eq P})%fset.
- case/fsubsetPn => i i_in_F i_notin_P.
  have i_in_base: i \in base by move: i_in_F; apply/fsubsetP/fsubset_subP.
  exists i; exists i_in_base => //.
  apply/val_inj/face_dim_eq => /=; last first.
  + by apply/succn_inj; rewrite -dimF -dim_facet.
  + by rewrite face_setE activeP /= fsub1set.
- suff: ~~ (pval P `<=` F).
  + by rewrite {1}[F]repr_active // activeP.
  + by move: dimF; apply/contra_eqN; move/dimS; rewrite -ltnS ltn_neqAle => /andP [].
Qed.

Lemma polyI_facet (F : {poly base}) :
  [poly0] `<` F -> (pval F `<` P) ->
    F = \polyI_(i : ({eq F} `\` {eq P})%fset) 'P^=(base; [fset (val i)]) :> 'poly[R]_n.
Proof.
move => F_prop0 F_prop_P.
set Q := (RHS).
have /fproperP [_ [i i_in i_notin]] : ({eq P} `<` {eq F})%fset
  by rewrite active_proper.
have {i_notin} {}i_in: i \in ({eq F} `\` {eq P})%fset
  by rewrite inE i_notin.
have Q_sub : Q `<=` P.
- by rewrite (RT.meets_max (j := [` i_in]%fset)) ?polyEq1 ?RT.leIl.
have <-: pval P `&` Q = Q by apply/RT.meet_r.
rewrite /Q polyEq_big_polyI; last by apply/pred0Pn; exists [` i_in]%fset.
rewrite {1}[P]repr_active ?polyEq_polyI; last by apply/RT.lt_trans: F_prop_P.
rewrite {1}[F]repr_active //=; apply/congr1.
apply/fsetP => e; apply/idP/idP.
- case: (boolP (e \in ({eq P} : {fset _}))).
  + by rewrite in_fsetU => ->.
  + move => e_notin e_in.
    rewrite inE; apply/orP; right.
    have {e_notin} {}e_in: e \in ({eq F} `\` {eq P})%fset by rewrite inE e_notin.
    apply/bigfcupP; exists ([`e_in]%fset).
    * by rewrite andbT /index_enum unlock -enumT mem_enum.
    * by rewrite in_fset1.
- rewrite inE; case/orP.
  + by apply/fsubsetP/activeS/poly_base_subset.
  + case/bigfcupP => e' _.
    rewrite in_fset1 => /eqP ->.
    by move: (fsvalP e'); rewrite in_fsetD => /andP[].
Qed.

End Facet.

Section PointedFacet.

Context {R : realFieldType} {n : nat}.

Lemma pointed_facet (P : 'poly[R]_n) :
  P `>` ([poly0]) -> pointed P -> exists2 F, F \in face_set P & dim P = (dim F).+1.
Proof.
elim/non_redundant_baseW: P => base non_redundant.
set P := 'P(base)%:poly_base => P_prop0 P_pointed.
case: (leqP (dim P) 1%N) => [dimP_le1 | dimP_gt1].
- rewrite dimN0 in P_prop0.
  have ->: dim P = 1%N by apply/anti_leq/andP; split.
  exists (pval (([poly0]%:poly_base) : {poly base})).
  + by rewrite face_setE RT.le0x.
  + by rewrite dim0.
- suff: ({eq P} `<` base)%fset.
  + move/fproperP => [_ [i i_base i_notin_eqP]].
    set F := 'P^=(base; [fset i]%fset)%:poly_base.
    exists (pval F); last exact: dim_facet.
    by rewrite face_setE RT.ltW ?facet_proper.
  + move: P_pointed; apply: contraTT; rewrite fsubset_properT negbK => /eqP eqP_eq_base.
    move: (P_prop0) dimP_gt1; rewrite [P]repr_active //=.
    rewrite eqP_eq_base polyEqT_affine => /proper0P [x x_in_aff].
    by rewrite (affine_orth x_in_aff) pointed_affine dim_affine ltnS lt0n dimv_eq0.
Qed.

End PointedFacet.

Section VertexSet.

Context {R : realFieldType} {n : nat}.

Definition vertex_set (P : 'poly[R]_n) :=
  [fset ppick F | F in face_lattice P & dim F == 1%N]%fset.

Lemma in_vertex_setP (P : 'poly[R]_n) x :
  (x \in vertex_set P) = ([pt x] \in face_lattice P).
Proof.
apply/imfsetP/idP => /=.
- move => [F] /andP [F_face /dim1P [y F_eq]].
  move: F_face; rewrite {}F_eq => ?.
  by rewrite ppick_pt => ->.
- move => pt_x_face.
  exists [pt x]; rewrite ?ppick_pt //=.
  by apply/andP; split; rewrite ?dim_pt.
Qed.

Lemma dim1_pt_ppick (P : 'poly[R]_n) :
  dim P = 1%N -> P = [pt (ppick P)].
Proof.
by move/eqP/dim1P => [? ->]; rewrite ppick_pt.
Qed.

Lemma face_dim1 (P Q : 'poly[R]_n) :
  Q \in face_lattice P -> dim Q = 1%N -> exists2 x, Q = [pt x] & x \in vertex_set P.
Proof.
move => Q_face dimQ1; exists (ppick Q).
- by apply/dim1_pt_ppick.
- by apply/in_imfset => /=; rewrite !inE Q_face dimQ1 eq_refl.
Qed.

Lemma vertex_setS (P Q : 'poly[R]_n) :
  P \in face_lattice Q -> (vertex_set P `<=` vertex_set Q)%fset.
Proof.
move => P_face.
apply/fsubsetP => x; rewrite 2!in_vertex_setP.
apply/fsubsetP; exact: faceS.
Qed.

Lemma vertex_set_face (P Q : 'poly[R]_n) :
  Q \in face_lattice P -> vertex_set Q = [fset x in (vertex_set P) | x \in Q]%fset.
Proof.
move => Q_face; apply/fsetP => x.
rewrite !inE !in_vertex_setP -pt_subset.
by rewrite (face_lattice_of_face Q_face) intervalE ?poly0_face ?RT.le0x.
Qed.

Lemma vertex_set_subset P : {subset (vertex_set P) <= P}.
Proof.
move => x; rewrite in_vertex_setP => /face_subset.
by rewrite pt_subset.
Qed.

Lemma vertex_set0 : (vertex_set ([poly0])) = fset0.
Proof.
apply/fsetP => x; rewrite in_vertex_setP.
by rewrite face0 !inE; apply/negbTE; rewrite -RT.lt0x pt_proper0.
Qed.

Lemma vertex_set1 (v : 'cV[R]_n) : vertex_set [pt v] = [fset v]%fset.
Proof.
apply/fsetP => x; apply/idP/idP.
- by move/vertex_set_subset; rewrite in_pt => /eqP ->; rewrite inE.
- rewrite inE => /eqP ->.
  by rewrite in_vertex_setP face_self.
Qed.

Lemma vertex_setN0 (P : 'poly[R]_n) :
  P `>` ([poly0]) -> pointed P -> vertex_set P != fset0.
Proof.
pose H k :=
  forall (P : 'poly[R]_n), dim P = k -> P `>` ([poly0]) -> pointed P -> vertex_set P != fset0.
suff: forall k, H k by move/(_ (dim P) P (erefl _)).
elim => [ Q | k IHk Q ].
- by rewrite dimN0 => ->.
- case: (posnP k) => [-> dimQ1 _ _ | k_gt0 dimQ _ Q_pointed].
  + apply/fset0Pn; exists (ppick Q).
    by rewrite [Q]dim1_pt_ppick ?ppick_pt ?vertex_set1 ?inE.
  + have : Q `>` [poly0] by rewrite dimN0 dimQ.
    move/pointed_facet/(_ _); move/(_ Q_pointed) => [F F_face].
    rewrite dimQ; move/succn_inj/esym => dimF.
    move: (IHk _ dimF); rewrite dimN0 dimF.
    move/(_ k_gt0 (face_pointed Q_pointed F_face)).
    apply/contra_neq => vtx_Q0.
    by move: (vertex_setS F_face); rewrite {}vtx_Q0 fsubset0 => /eqP ->.
Qed.

Lemma opt_vertex (P : 'poly[R]_n) c :
  pointed P -> bounded P c -> exists2 x, x \in vertex_set P & x \in argmin P c.
Proof.
move => P_pointed c_bounded.
set F := argmin P c.
have F_face : F \in face_set P by apply/argmin_in_face_lattice.
have F_pointed : pointed F by apply/(pointedS (argmin_subset _ _)).
have F_prop0 : F `>` [poly0] by rewrite -bounded_argminN0.
move/(vertex_setN0 F_prop0)/fset0Pn: F_pointed => [x x_vtx_F].
exists x.
- by apply/(fsubsetP (vertex_setS _)): x_vtx_F.
- by apply/vertex_set_subset.
Qed.

End VertexSet.

Section FaceSetGraded.

Context {R : realFieldType} {n : nat} .

Lemma dim_proper (P Q : 'poly[R]_n) :
  (P `<=` Q) -> (dim P < dim Q)%N -> (P `<` Q).
Proof.
rewrite RT.lt_neqAle => ->; rewrite andbT.
by apply/contraTneq; rewrite -leqNgt => ->.
Qed.

Implicit Type P : 'pointed[R]_n.

Lemma graded (P0 : 'pointed[R]_n) (Q Q' : 'poly[R]_n) :
  Q \in face_lattice P0 -> Q' \in face_lattice P0 ->
  Q `<=` Q' -> ((dim Q).+1 < (dim Q'))%N ->
    exists2 F, F \in face_lattice P0 & Q `<` F `<` Q'.
Proof.
move => Q_face Q'_face Q_sub_Q'.
have Q'_pointed : pointed Q' by apply/(face_pointed (valP P0)).
have {Q_face Q_sub_Q'} : Q \in face_lattice Q'.
  by rewrite (face_lattice_of_face Q'_face) mem_itv.
move: Q' Q'_face Q'_pointed Q; elim/non_redundant_baseW => base non_redundant.
set P := 'P(base)%:poly_base => P_face P_pointed Q.
case/faceP => {}Q Q_sub_P dim_lt.
have {Q_sub_P} Q_prop_P : pval Q `<` pval P.
- rewrite dim_proper //.
  by apply/ltn_trans: dim_lt.
have P_prop0 : P `>` [poly0] by apply: (RT.le_lt_trans (RT.le0x (pval Q))).
case: (emptyP Q) dim_lt => [ -> | Q_prop0].
- rewrite dim0 => dimP_gt1.
  case/fset0Pn : (vertex_setN0 P_prop0 P_pointed) => x.
  rewrite in_vertex_setP => x_vtx.
  exists [pt x].
  + by move: x_vtx; apply/fsubsetP/(faceS P_face).
  + by rewrite pt_proper0 dim_proper ?dim_pt ?face_subset.
- have eqQ_prop_eqP : ({eq P} `<` {eq Q})%fset by apply/active_proper.
  move/fproperP: (eqQ_prop_eqP) => [_ [i i_in_eqQ i_notin_eqP]].
  have i_in_base: (i \in base) by move: (i) i_in_eqQ; apply/fsubsetP: (valP {eq Q}).
  set S := 'P^=(base; [fset i])%:poly_base => dim_lt.
  have Q_prop_S : pval Q `<` pval S.
  + rewrite dim_proper ?activeP ?fsub1set ?i_in_eqQ //.
    by move: dim_lt; rewrite (dim_facet _ _ _ i_notin_eqP).
  have S_prop_P : pval S `<` pval P.
  + rewrite RT.lt_neqAle andbC; apply/andP; split.
    * by rewrite /= -polyEq0; apply: polyEq_antimono.
    * move: i_notin_eqP; apply: contraNneq => /pval_inj <-.
      rewrite -fsub1set; exact: active_polyEq.
  exists (pval S).
  + apply/(fsubsetP (faceS P_face)).
    by rewrite face_setE RT.ltW.
  + by apply/andP; split.
Qed.

Lemma fbot_face_lattice (P : 'poly[R]_n) :
  \fbot_(face_lattice P) = [poly0].
Proof.
apply/(RT.le_anti poly_preLattice)/andP; split.
- by rewrite le0f ?poly0_face.
- by rewrite RT.le0x.
Qed.

Lemma ftop_face_lattice (P : 'poly[R]_n) :
  \ftop_(face_lattice P) = P.
Proof.
apply/(RT.le_anti poly_preLattice)/andP; split.
- by apply/face_subset/mem_ftop.
- by rewrite lef1 ?face_self.
Qed.

Lemma dim_rank (P0 : 'pointed[R]_n) : rank (face_lattice P0) (@dim R n).
Proof.
split; [| exact: face_dim_lt | exact: graded].
by rewrite fbot_face_lattice dim0.
Qed.

(*
 * OBSOLETE
Lemma dimfs0 P : dim (val (0%O : face_set P)) = 0%N.
Proof. by rewrite dim0. Qed.

Lemma homo_dim P (x y : face_set P) :
  x < y -> (dim (val x) < dim (val y))%N.
Proof.
by apply: (face_dim_lt (valP _) (valP _)).
Qed.

Lemma dim_graded P (x y : face_set P) :
  x <= y -> ((dim (val x)).+1 < dim (val y))%N -> exists z, x < z < y.
Proof.
rewrite leEfaces => /(graded (valP _) (valP _)) h /h => [[F] F_in F_lt].
by exists ([` F_in]%fset); rewrite !ltEfaces.
Qed.

Definition face_set_gradedFinLatticeMixin P :=
  GradedFinLatticeMixin (dimfs0 P) (@homo_dim P) (@dim_graded P).
Canonical face_set_gradedFinLatticeType P :=
  Eval hnf in GradedFinLatticeType (face_set P) (face_set_gradedFinLatticeMixin P).

Lemma atom_faceP (P : 'pointed[R]_n) (F : face_set P) :
  reflect
    (exists2 x : 'cV_n, x \in vertex_set P & val F = [pt x])
    (atom F).
Proof.
rewrite atomE /rank /=; apply: (iffP eqP).
+ by move/face_dim1 => /(_ _ (fsvalP _)) [x ->]; exists x.
+ by case=> x xP ->; rewrite dim_pt.
Qed.
*)
End FaceSetGraded.

Section Minkowski.

Context {R : realFieldType} {n : nat}.

Lemma conv_vertex_set (P : 'poly[R]_n) :
  compact P -> P = conv (vertex_set P).
Proof.
case: (emptyP P) => [-> _| P_prop0 P_compact].
- by rewrite vertex_set0 conv0.
- apply/poly_eqP => x; apply/idP/idP.
  + apply/contraTT.
    move/separation => [e x_notin_hs conv_sub].
    have e_bounded : bounded P e.1 by apply/compactP.
    move/compact_pointed/opt_vertex: P_compact.
    move/(_ _ e_bounded) => [y].
    move/in_conv/(poly_leP conv_sub) => y_in_e y_in_argmin.
    move: x_notin_hs; apply/contraNN => x_in_P.
    rewrite !in_hs in y_in_e *; apply/(le_trans y_in_e).
    by apply/(argmin_lower_bound y_in_argmin).
  + apply/poly_leP/conv_subset.
    exact: vertex_set_subset.
Qed.

(*
Lemma face_atomistic (P : 'compact[R]_n) (F : face_set P) : atomistic F.
Proof.
pose S := vertex_set (val F).
have h x : x \in S -> [pt x] \in face_set P.
+ move=> xS; rewrite -in_vertex_setP.
  by apply/fsubsetP/vertex_setS/valP: x xS.
apply/atomisticP => /=; exists [set [` h _ (valP x)]%fset | x : S].
+ move=> F' /imsetP[/= x xS -> /=]; apply/atom_faceP.
  case: x xS => /= x xS vxS; exists x => //.
  by rewrite in_vertex_setP h.
rewrite (rwP eqP) RT.eq_le [leo: <=%P] -(rwP andP); split; last first.
+ apply/joinsP=> /= F' /imsetP[/= x xS ->].
  rewrite leEfaces pt_subset.
  by apply: vertex_set_subset.
rewrite leEfaces [val F]conv_vertex_set; last first.
+ by apply/(subset_compact (valP P))/(lex1 F).
apply: conv_subset => /= c cF.
have: c \in fsval [` h _ cF]%fset by rewrite in_pt.
apply: poly_leP; rewrite -poly_leE -leEfaces join_sup //.
by apply/imsetP; exists [` cF]%fset => //; apply: val_inj.
Qed.*)

Lemma subset_hp (V : {fset 'cV[R]_n}) :
  (0 < #|` V | <= n)%N -> exists2 e : lrel[R]_n, (e.1 != 0) & {subset V <= [hp e]}.
Proof.
rewrite cardfs_gt0 => /andP [/fset0Pn [v v_in] cardV_le].
pose U := <<[seq w - v | w <- (V `\ v)%fset]>>%VS.
have: ((\dim U).+1 <= n)%N.
- apply/leq_trans: cardV_le.
  have ->: #|` V| = #|` (V `\  v)|%fset.+1%N by rewrite (@cardfsD1 _ v) v_in.
  rewrite ltnS; apply/(leq_trans (dim_span _)).
  by rewrite size_map.
rewrite -subn_gt0 -dim_orthv lt0n dimv_eq0 => h.
pose c := vpick (U^OC)%VS.
pose e := [< c, '[c,v] >]; exists e; first by rewrite vpick0.
move => w; case/altP : (w =P v) => [-> _| w_neq_v w_in_V].
- by rewrite in_hp.
- rewrite in_hp /=.
  have ->: w = v + (w - v) by rewrite addrCA addrN addr0.
  rewrite vdotDr; suff ->: '[c, w-v] = 0 by rewrite addr0.
  rewrite vdotC; apply/(orthvP (V := U)); first exact: memv_pick.
  by rewrite memv_span //; apply/map_f; rewrite !inE w_neq_v.
Qed.

Lemma card_vertex_set (P : 'poly[R]_n):
  compact P -> (dim P > n)%N -> (#|` vertex_set P | > n)%N.
Proof.
move => P_compact dimP.
have P_prop0: P `>` [poly0] by rewrite dimN0; apply/leq_trans: dimP.
move: dimP; apply: contraTT; rewrite -2!leqNgt => card_vtx.
have {card_vtx}: (0 < #|` vertex_set P | <= n)%N.
- rewrite card_vtx andbT.
  by rewrite cardfs_gt0 vertex_setN0 ?compact_pointed.
move/subset_hp => [e /negbTE e_neq0 /conv_subset].
rewrite -conv_vertex_set // => sub.
move/dimS: (sub); rewrite dim_hp ?e_neq0 //.
by apply/RT.lt_le_trans: sub.
Qed.

End Minkowski.

Section Coatomistic.

Context {R : realFieldType} {n : nat}.

Lemma card_vertex_set_gt1 (P : 'poly[R]_n) :
  compact P -> (dim P > 1)%N -> (#|` vertex_set P | > 1)%N.
Proof.
move => P_compact.
apply/contraTT; rewrite -2!ltnNge !ltnS.
case: (emptyP P) => [->| P_prop0 card_le1]; first by rewrite dim0.
have /eqP/cardfs1P [v]: #|` vertex_set P| = 1%N.
- apply/anti_leq/andP; split => //.
  by rewrite cardfs_gt0 vertex_setN0 ?compact_pointed.
rewrite {2}[P]conv_vertex_set // => ->.
by rewrite conv_pt dim_pt.
Qed.

Lemma polyEqT_poly0 (base : base_t[R,n]) (P : {poly base}) :
  compact P -> (dim P > 1)%N -> 'P^=(base; base) = [poly0].
Proof.
move/card_vertex_set_gt1 => h /h card_gt1.
have: (0 < #|` vertex_set P|)%N by apply/ltn_trans: card_gt1.
rewrite cardfs_gt0 => /fset0Pn [v v_in].
have: (0 < #|` (vertex_set P `\  v)%fset |)%N
  by rewrite (@cardfsD1 _ v) v_in ltnS in card_gt1.
rewrite cardfs_gt0 => /fset0Pn [w w_in].
apply/eqP; rewrite -RT.lex0.
have <-: [pt v] `&` [pt w] = [poly0].
- apply/poly_eqP => x; rewrite in_polyI 2!in_pt !inE.
  apply/negbTE/negP; move/andP => [/eqP -> /eqP v_eq_w].
  by move: w_in; rewrite v_eq_w !inE eq_refl.
move: v_in (pt_proper0 v); rewrite in_vertex_setP.
case/faceP => Q Q_sub Q_prop0.
move: w_in (pt_proper0 w); rewrite inE => /andP[_].
rewrite in_vertex_setP; case/faceP => Q' Q'_sub Q'_prop0.
rewrite [Q]repr_active // [Q']repr_active //.
rewrite polyEq_polyI polyEq_antimono //.
by apply/fsubset_subP.
Qed.

(*
Lemma face_coatomistic (P : 'compact[R]_n) (F : face_set P) :
  coatomistic F.
Proof.
case: P F; case.
elim/non_redundant_baseW => base non_redundant P_pointed P_compact /=.
set P := Pointed P_pointed => F.
set L := [gradedFinLatticeType of face_set P].
case/altP: (F =P 0)%O => [-> | F_neq0]; last first.
apply/coatomisticP.
case/altP: (F =P 1)%O => [-> | F_neq_P].
- exists set0; first by move => x; rewrite inE.
  by rewrite big_pred0 //; move => x; rewrite inE.
- pose F' := insubd (val P)%:poly_base (val F).
  have F'_eq: F' = val F :> 'poly[R]_n.
  + by rewrite /F' /insubd insubT //= (face_set_has_base (valP F)).
  have F'_prop_P : pval F' `<` P.
  + rewrite lt_neqAle andbC poly_base_subset /=.
    by move: F_neq_P; apply/contra_neq => ?; apply/val_inj => /=; rewrite -F'_eq.
  have F'_prop0 : F' `>` [poly0].
  + rewrite lt0x.
    by move: F_neq0; apply/contra_neq => ?; apply/val_inj => /=; rewrite -F'_eq.
  have h i : i \in base -> 'P^=(base; [fset i]) \in face_set P.
  + by move => ?; rewrite face_setE /= polyEq_antimono0.
  pose S := [set [` h _ (valP i)]%fset |
    i : base & (val i \in ({eq F'} `\` {eq (val P)%:poly_base})%fset) ].
  exists S; last first.
  + apply/le_anti/andP; split.
    * apply/meetsP => i /imsetP [{}i i_in -> /=].
      rewrite leEfaces -F'_eq /=.
      move: (fsvalP i) => ?; rewrite activeP /= fsub1set.
      by move: i_in; rewrite in_set in_fsetD => /andP[].
    * rewrite leEfaces -F'_eq polyI_facet //.
      - apply/RT.meetsP => i _.
        + have i_in_base : val i \in base.
          * move: (valP i); rewrite in_fsetD => /andP[_].
            by apply/fsubsetP/fsubset_subP.
        suff: (\meet_(x in S) x <= [` h _ i_in_base]%fset)%O.
          rewrite leEfaces; apply: le_trans.
          by apply: lexx.
        apply/meets_inf/imsetP; exists [` i_in_base]%fset => //.
        + by rewrite in_set /= fsvalP.
        + by apply/val_inj => /=.
  +  move => Q; case/imsetP => i; rewrite in_set inE => /andP [i_notin _ ->].
     rewrite (@coatomE _ L).
     rewrite /rank /= -(rwP eqP) (dim_facet _ _ _ i_notin) ?fsvalP //.
       by apply/lt_trans: F'_prop_P.
apply/coatomisticP.
case: {2}(dim 'P(base)) (erefl (dim 'P(base))) => [dimP0|].
- exists set0; first by move => ?; rewrite in_set0.
  rewrite big_pred0; last by move => ?; rewrite in_set0.
  symmetry; apply/eqP.
  by rewrite -(@rank_eq0 _ L) /rank /= dimP0.
- case => [dimP1 |k dimP].
  + exists [set 0%O].
    * move => ?; rewrite in_set1 => /eqP ->.
      by rewrite (@coatomE _ L) !/rank /= dimP1 dim0.
    * by rewrite (big_pred1 0%O) // => ?; rewrite !inE.
  + move: (leq_addr k 2); rewrite add2n -{}dimP => dimP_gt1.
    have h i : i \in base -> 'P^=(base; [fset i]) \in face_set P.
    * by move => ?; rewrite face_setE /= polyEq_antimono0.
    have P_prop0: 'P(base) `>` [poly0] by move: dimP_gt1; rewrite dimN0; apply/ltn_trans.
    pose E := {eq ('P(base))%:poly_base} : {fset _}.
    have E_prop : (E `<` base)%fset.
    * rewrite /E fsubset_properT; move: (P_prop0); apply/contraTneq.
      have {2}->: 'P(base) = 'P(base)%:poly_base by [].
      rewrite {2}['P(base)%:poly_base]repr_active //= => ->.
      by rewrite (polyEqT_poly0 P_compact) ?ltxx.
    pose S := [set [` h _ (valP i)]%fset | i : base & (val i \notin E) ].
    exists S; last first.
    - apply/le_anti/andP; split; first by apply/le0x.
      rewrite leEfaces /= -(polyEqT_poly0 P_compact) //=.
      suff ->: 'P^=(base; base) =
        \polyI_(i : base | (val i) \notin E) 'P^=(base; [fset (val i)]).
      + apply/RT.meetsP => i i_notin.
        suff: (\meet_(x in S) x <= [` h _ (valP i)]%fset)%O.
          by rewrite leEfaces /=; apply/le_trans.
        apply/meets_inf/imsetP; exists i => //; by rewrite in_set i_notin.
      + rewrite polyEq_big_polyI;
        last by apply/pred0Pn; move/fproperP: E_prop => [_] [e e_in ?]; exists [` e_in]%fset.
        have ->: 'P^=(base; base) = 'P^=(base; (base `\` E) `|` E).
        * apply/congr1; apply/fsetP => e; rewrite in_fsetU.
          apply/idP/idP.
          - rewrite in_fsetD => ->; rewrite andbT; by case: (e \in E).
          - case/orP.
            by rewrite in_fsetD => /andP [].
            rewrite /E; apply/fsubsetP/fsubset_subP.
        rewrite -polyEq_polyI {3}/E.
        move: (@repr_active _ _ _ 'P(base)%:poly_base) => /(_ P_prop0)/(congr1 val) //= <-.
        have /meet_l ->: 'P^=(base; base `\` E) `<=` 'P(base) by apply/polyEq_antimono0.
        apply/congr1/fsetP => e; apply/idP/idP.
        - rewrite in_fsetD => /andP [e_notin e_in].
          apply/bigfcupP; exists ([`e_in]%fset) => //.
          * by rewrite /index_enum unlock -enumT mem_enum /=.
          * by rewrite in_fset1.
        - case/bigfcupP => e'; rewrite in_fset1 => /andP [_ e'_not_in] /eqP ->.
          by rewrite in_fsetD e'_not_in /= fsvalP.
    - move => Q; case/imsetP => i; rewrite in_set => i_notin ->.
      rewrite (@coatomE _ L).
      by rewrite /rank /= -(rwP eqP) (dim_facet _ _ _ i_notin) ?fsvalP //.
Qed.
 *)

End Coatomistic.

Section SeparationVertex.

Context {R : realFieldType} {n : nat}.

Lemma sep_vertex (P : 'poly[R]_n) v :
  compact P -> v \in vertex_set P -> v \notin conv (vertex_set P `\ v)%fset.
Proof.
move => P_compact.
rewrite in_vertex_setP => /face_argmin/(_ (pt_proper0 _)) [c c_bounded pt_eq].
pose S := [seq '[c,x] | x <- (vertex_set P `\ v)%fset].
pose α := min_seq S ('[c,v]+1%R).
have v_notin: v \notin [hs [<c, α>]].
- rewrite /α; case: min_seqP => [| ? [/mapP [z] z_in -> _]].
  + by rewrite in_hs -ltNge cpr_add ltr01.
  + move: z_in; rewrite 2!inE => /andP [z_neq_v /vertex_set_subset z_in].
    have /(notin_argmin c_bounded z_in): z \notin argmin P c by rewrite -pt_eq in_pt.
    rewrite in_hsN in_hs /=.
    suff ->: '[c,v] = opt_value c_bounded by [].
    move: (argmin_opt_value c_bounded).
    rewrite -pt_eq => /poly_leP/(_ _ (in_pt_self _)).
    by rewrite inE /= => /eqP ->.
- suff: conv (vertex_set P `\ v)%fset `<=` [hs [<c,α >]].
  + by apply/contraL => v_in; apply/poly_lePn; exists v.
  + apply/conv_subset => w w_in.
    by rewrite inE /= /α; apply/min_seq_ler/mapP; exists w.
Qed.

Lemma vertex_set_conv_subset (V : {fset 'cV[R]_n}) : (vertex_set (conv V) `<=` V)%fset.
Proof.
set P := conv V.
apply/fsubsetP => v v_vtx.
move/vertex_set_subset: (v_vtx) => v_in.
move: v_vtx; rewrite in_vertex_setP => /face_argmin/(_ (pt_proper0 _)) => [[c] c_bounded].
move/in_convP: v_in => {v} [w w_supp ->].
set v := combine w => eq_argmin.
have /forallPn [x]: ~~ [forall v : V, val v \notin [hs -[<c, opt_value c_bounded>]]].
- move: (in_pt_self v); rewrite eq_argmin argmin_polyIN in_polyI => /andP [_].
  apply/contraL; move/forallP => h.
  suff: v \in [predC [hs -[<c, opt_value c_bounded>]]] by rewrite !inE.
  apply/convexW; first exact: hsC_convex.
  move => x /(fsubsetP w_supp) x_in.
  have ->: x = val [` x_in]%fset by [].
  by apply/h.
rewrite negbK => x_in.
have {x_in}: val x \in argmin P c by rewrite argmin_polyIN inE x_in andbT in_conv ?fsvalP.
rewrite -eq_argmin in_pt => /eqP <-; exact: fsvalP.
Qed.

Definition sep_hp (e : lrel[R]_n) (V : {fset 'cV_n}) (x : 'cV_n) :=
  (x \notin [hs e]) && [forall v : V, (val v) \notin [hs -e]].

Notation "[ e 'separates' x 'from' V ]" := (sep_hp e V x) : poly_scope.

Lemma sep_hpP {e : lrel[R]_n} {V : {fset 'cV_n}} {x : 'cV_n} :
  reflect ((x \notin [hs e]) /\ (forall y, y \in conv V -> y \notin [hs -e]))
          ([e separates x from V]).
Proof.
apply: (iffP andP) => [[? /forallP h] | [? h]]; split => //.
- move => y /in_convP [w w_supp ->].
  suff: combine w \in [predC [hs -e]] by rewrite !inE.
  apply/convexW; first exact: hsC_convex.
  move => v /(fsubsetP w_supp) v_in.
  have ->: v = val [` v_in]%fset by []; apply/h.
- by apply/forallP => v; apply/h/in_conv/fsvalP.
Qed.

Lemma conv_sep_hp (V : {fset 'cV_n}) (x : 'cV_n) :
  x \notin conv V -> exists e : lrel, [e separates x from V].
Proof.
move/separation => [e x_notin /poly_leP sub].
rewrite in_hs -ltNge in x_notin.
pose e' := [<e.1, ('[e.1,x]+e.2)/2%:R >].
exists e'; apply/andP; split.
- by rewrite in_hs -ltNge /e' /= midf_lt.
- apply/forallP => v; rewrite in_hsN -ltNge /e' /=.
  move/in_conv/sub: (fsvalP v); rewrite in_hs.
  by apply/lt_le_trans; rewrite midf_lt.
Qed.

End SeparationVertex.

Notation "[ e 'separates' x 'from' V ]" := (sep_hp e V x) : poly_scope.

Section FaceSegment.

Context {R : realFieldType} {n : nat} .

Lemma vertex_set_segm (v v' : 'cV[R]_n) :
  vertex_set [segm v & v'] = [fset v; v']%fset.
Proof.
set V := [fset _; _]%fset; set S := conv _.
have sub: (vertex_set S `<=` V)%fset by apply/vertex_set_conv_subset.
apply/eqP; rewrite eqEfcard sub /=.
move: (conv_vertex_set (compact_conv [fset v; v']%fset)); rewrite -/S.
apply/contra_eqT => /=; rewrite -ltnNge cardfs2 ltnS.
case/altP: (#|` vertex_set S| =P 0%N) => /= [ /cardfs0_eq -> _|].
- by rewrite conv0 -RT.lt0x segm_prop0.
- rewrite -lt0n => card_gt0.
  case/altP: (v =P v') => /= [_| neq card_le1].
  + by rewrite leqn0 => /eqP card_eq0; rewrite card_eq0 in card_gt0.
  + have {card_gt0} {card_le1} /eqP/cardfs1P [x ->]: #|` vertex_set S| = 1%N by apply/anti_leq/andP; split.
    apply/eqP; move/(congr1 (@dim R n)).
    by rewrite conv_pt dim_pt dim_segm neq.
Qed.

Lemma face_lattice_segm (v v' : 'cV[R]_n) :
  face_lattice [segm v & v'] = [fset [poly0]; [pt v]; [pt v']; [segm v & v']]%fset :> {fset _}.
Proof.
set S := conv _.
apply/eqP; rewrite eqEfsubset; apply/andP; split; last first.
- apply/fsubsetP => F; rewrite !inE -!orbA; move/or4P.
  case; move/eqP ->;
    by rewrite ?poly0_face ?face_self -?in_vertex_setP ?vertex_set_segm ?inE ?eq_refl ?orbT.
- apply/fsubsetP => F F_face; rewrite !inE -!orbA.
  case: {2}(dim F) (erefl (dim F)).
  + by move/dim_eq0 ->; rewrite eq_refl.
  + case. move/(face_dim1 F_face) => [x ->].
    by rewrite vertex_set_segm !inE => /orP; case => /eqP ->; rewrite eq_refl /= ?orbT.
  + case. move => dimF2.
    have /(face_dim_geq F_face) ->: (dim F >= dim S)%N.
    * by rewrite dimF2 dim_segm; apply/(leq_ltn_trans (leq_b1 _)).
    * by rewrite eq_refl !orbT.
  + move => k dimF_eq; move: (face_dim_leqif_eq F_face).1; rewrite dim_segm dimF_eq ltnS.
    by move/leq_trans/(_ (leq_b1 _)); rewrite -ltn_predRL /= ltn0.
Qed.

End FaceSegment.

Section VertexFigureHyp.

Context {R : realFieldType} {n : nat}.

Definition vf_hyp (P : 'poly[R]_n) (v : 'cV[R]_n) (e : lrel[R]_n) :=
  ((v \in vertex_set P) * [e separates v from ((vertex_set P) `\ v)%fset])%type.

End VertexFigureHyp.

Module VertexFigurePolyBase.
Section VertexFigurePolyBase.

Context {R : realFieldType} {n : nat}.

Variable (base : base_t[R,n]) (P : {poly base}) (v : 'cV[R]_n) (e0 : lrel[R]_n).
Hypothesis P_compact : compact P.
Hypothesis hyp : vf_hyp P v e0.
Let v_vtx := hyp.1.
Let sep_v := (sep_hpP hyp.2).1.
Let sep_other := (sep_hpP hyp.2).2.

Let L := [< [pt v]; P >]_(face_lattice P).
Let Φ := (slice e0).

Lemma vf_vtx (F : 'poly[R]_n) :
  F \in L -> v \in vertex_set F.
Proof.
rewrite intervalE ?face_self -?in_vertex_setP //;
  last by rewrite pt_subset vertex_set_subset.
case/and3P=> /vertex_set_face ->.
by rewrite !inE v_vtx pt_subset => ->.
Qed.

Lemma vf_L_v_in (F : 'poly[R]_n) :
  F \in L -> v \in F.
Proof.
rewrite intervalE -?in_vertex_setP ?face_self //;
  last by rewrite pt_subset vertex_set_subset.
by case/and3P=> _; rewrite pt_subset.
Qed.

Lemma vf_L_prop0 (F : 'poly[R]_n) :
  F \in L -> F `>` [poly0].
by move/vf_L_v_in => ?; apply/proper0P; exists v.
Qed.

Lemma vf_L_face (F : 'poly[R]_n) :
  F \in L -> F \in face_lattice P.
Proof. exact: itv_subset. Qed.

Lemma vf_L_other_pt (F : 'poly[R]_n) :
  F \in L -> (dim F > 1)%N -> exists2 x, x \in F & x \notin [hs -e0].
Proof.
move => F_in_L dimF_gt1.
rewrite [F]conv_vertex_set ?(face_compact P_compact) ?vf_L_face // in dimF_gt1.
suff /fsubsetPn [w w_vtx w_neq] : ~~ (vertex_set F `<=` [fset v])%fset.
- exists w; first by move: w_vtx => /vertex_set_subset w_in_F.
  apply/sep_other/in_conv; rewrite inE w_neq /=.
  by move: w_vtx; apply/fsubsetP/vertex_setS/vf_L_face.
- move: dimF_gt1; apply: contraTN => sub.
  suff ->: vertex_set F = [fset v]%fset by rewrite conv_pt dim_pt.
  by apply/eqP; rewrite eqEfsubset fsub1set ?vf_vtx ?andbT.
Qed.

Lemma vf_prop0 (F : 'poly[R]_n) :
  F \in L -> (dim F > 1)%N -> (Φ F) `>` [poly0].
Proof.
move => F_in_L dimF_gt1.
move: (vf_L_other_pt F_in_L dimF_gt1) => [w w_in_F w_notin].
have w_in_hs : w \in [hs e0] by apply/hsN_subset/w_notin.
move: (hp_itv w_in_hs sep_v) => [α /ltW_le α01].
set x := _ + _ => x_in_hp; apply/proper0P; exists x.
by rewrite in_slice x_in_hp mem_poly_convex ?vf_L_v_in.
Qed.

Lemma vf_eq (F : {poly base}) :
  (pval F) \in L -> (dim F > 1)%N -> {eq (Φ F)%:poly_base} = (e0 +|` {eq F})%:fsub.
Proof.
move => F_in_L dimF_gt1.
apply/fsubset_inj/eqP; rewrite eq_sym eqEfsubset active_slice.
apply/fsubset_fsubsetP => i; rewrite inE.
move/orP; case => [| i_in_base];
  first by rewrite in_fset1 => /eqP -> _; rewrite inE in_fset1 eq_refl.
apply/contraTT; rewrite inE negb_or => /andP [_].
rewrite in_active // => /poly_lePn => [[x] x_in_F x_notin_hp].
(* TODO : remove code duplication by introducing the right suff *)
case: (boolP (x \in [hs -e0])) => [x_in | /hsN_subset x_in].
- move: (vf_L_other_pt F_in_L dimF_gt1) => [w w_in_F w_notin].
  move: (hp_itv x_in w_notin) => [α α01].
    set y := _ + _; rewrite hpN => y_in_hp.
    rewrite in_active ?inE ?i_in_base ?orbT //; apply/poly_lePn; exists y.
    + by rewrite in_slice y_in_hp; apply/mem_poly_convex => //; apply/ltW_le.
      move: x_notin_hp; apply/contraNN/hp_extremeL => //.
      by apply/(poly_leP (poly_base_subset_hs _ _)) : x_in_F.
      by apply/(poly_leP (poly_base_subset_hs _ _)) : w_in_F.
- move: (hp_itv x_in sep_v) => [α α01].
  set y := _ + _ => y_in_hp.
  rewrite in_active ?inE ?i_in_base ?orbT //; apply/poly_lePn; exists y.
  + by rewrite in_slice y_in_hp mem_poly_convex ?vf_L_v_in ?ltW_le.
  + move: x_notin_hp; apply/contraNN/hp_extremeL => //.
    by apply/(poly_leP (poly_base_subset_hs _ _)) : x_in_F.
    by move/vf_L_v_in: F_in_L; apply/(poly_leP (poly_base_subset_hs _ _)).
Qed.

Lemma vf_slice_pt : Φ ([pt v]) = [poly0].
Proof.
apply/(RT.le_anti [leo:<=%P]); apply/andP; split; last exact: RT.le0x.
apply/poly_leP => x; rewrite in_slice in_pt in_poly0 andbC.
move/andP => [/eqP -> /(poly_leP (hp_subset_hs _))].
by move/negbTE: sep_v ->.
Qed.

Lemma vf_dim1 (F : 'poly[R]_n) :
  F \in L -> (dim F <= 1)%N -> F = ([pt v]) :> 'poly[R]_n.
Proof.
move => F_in_L dim_le1.
apply/eqP; rewrite eq_sym -(geq_leqif (face_dim_leqif_eq _)) ?dim_pt //.
by rewrite -in_vertex_setP vf_vtx.
Qed.

Lemma vf_im (F : 'poly[R]_n) :
  F \in L -> (Φ F) \in face_lattice (Φ P).
Proof.
move => F_in_L; move: (F_in_L); move/vf_L_face: F_in_L.
case/faceP => {}F F_sub_P F_in_L.
case: (ltnP 1 (dim F)) => [dim_gt1 | ?].
- by rewrite face_setE sliceS.
- by rewrite [pval F]vf_dim1 ?vf_slice_pt ?poly0_face.
Qed.

Lemma vf_P_in_L : pval P \in L.
Proof. by apply/mem_itvR; rewrite ?face_self ?pt_subset ?vertex_set_subset. Qed.

Lemma vf_mem_v (F : 'poly[R]_n) :
  F \in face_lattice P -> Φ F `>` ([poly0]) -> v \in F.
Proof.
move => F_face PhiF_prop0; apply/vertex_set_subset; move: PhiF_prop0.
apply/contraTT; rewrite RT.lt0x => v_notin; rewrite negbK.
apply/eqP; apply/(RT.le_anti [leo: <=%P]); apply/andP; split; last exact: RT.le0x.
rewrite [F]conv_vertex_set ?(face_compact P_compact) //.
apply/poly_leP => x; rewrite in_slice andbC => /andP [/in_convP [y /fsubsetP y_supp ->] in_hp].
have: combine y \in [predC [hs -e0]].
- apply/convexW; first exact: hsC_convex.
  move => w /y_supp w_vtx; rewrite inE.
  apply/sep_other/in_conv; rewrite !inE.
  apply/andP; split; move: w_vtx.
  + by apply/contraTneq => ->.
  + by apply/fsubsetP/vertex_setS.
rewrite !inE /= vdotNl in in_hp *.
by move/eqP: in_hp ->; rewrite lexx.
Qed.

Lemma vf_e0_notin_eq (F : {poly base}) :
  pval F \in L -> e0 \notin ({eq F} : {fset _}).
Proof.
apply: contraL => /poly_base_subset_hp/poly_leP sub.
by move: sep_v; apply/contraNN; move/vf_L_v_in/sub; apply/(poly_leP (hp_subset_hs _)).
Qed.

Lemma vf_surj :
  Φ @` (L : {fset _}) = face_lattice (Φ P).
Proof.
apply/fsetP => F; apply/imfsetP/idP=> [[?] ? ->|].
- exact: vf_im.
- move => F_face.
  case: (emptyP F) => [->| F_prop0].
  + exists ([pt v]); rewrite ?vf_slice_pt //.
    by apply/mem_itv; rewrite -?in_vertex_setP // ?pt_subset ?vertex_set_subset.
  + move: F_face F_prop0; case/faceP => {}F F_sub F_prop0.
    set F' := 'P^=(base; ({eq F} `|- e0))%:poly_base.
    have F_eq : F = (Φ F') :> 'poly[R]_n.
    * rewrite {1}[F]repr_active //= /Φ slice_polyEq /fslice fsetD1K //.
      rewrite in_active ?inE ?eq_refl //.
      by apply/(RT.le_trans F_sub)/RT.leIl.
    rewrite F_eq; exists (pval F') => //.
    suff F'_face: pval F' \in face_lattice P.
    * apply/mem_itv => //; last by rewrite face_subset.
      by rewrite pt_subset vf_mem_v -?F_eq ?face_subset.
    * rewrite face_setE [P]repr_active ?vf_L_prop0 ?vf_P_in_L ?polyEq_antimono //.
      move/activeS/(fsubset_trans (active_slice _ _))/(fsetSD [fset e0]%fset): F_sub.
      by rewrite fsetU1K ?vf_e0_notin_eq ?vf_P_in_L.
Qed.

Lemma vf_inj : {in L &, injective Φ}.
Proof.
move => F F'.
move => F_in_L; move: (F_in_L); move/vf_L_face: F_in_L; case/faceP => {}F F_sub_P F_in_L.
move => F'_in_L; move: (F'_in_L); move/vf_L_face: F'_in_L; case/faceP => {}F' F'_sub_P F'_in_L.
case: (ltnP 1 (dim F)) => [dimF_gt1 | ?]; case: (ltnP 1 (dim F')) => [dimF'_gt1 | ?]; last first.
- by rewrite [pval F]vf_dim1 1?[pval F']vf_dim1.
- rewrite [pval F]vf_dim1 ?vf_slice_pt // => eq.
  by move: (vf_prop0 F'_in_L dimF'_gt1); rewrite -eq RT.ltxx.
- rewrite [pval F']vf_dim1 ?vf_slice_pt // => eq.
  by move: (vf_prop0 F_in_L dimF_gt1); rewrite eq RT.ltxx.
- move/pval_inj/(congr1 active); rewrite ?vf_eq //=.
  rewrite {3}[F]repr_active 1?{3}[F']repr_active ?vf_L_prop0 //.
  move/(congr1 (fun (x : {fsubset _}) => (x `|- e0))) => /=.
  by rewrite !/funslice !/fslice !fsetU1K ?vf_e0_notin_eq // => ->.
Qed.

Lemma vf_dim (F : 'poly[R]_n) :
  F \in L -> (dim F = (dim (Φ F)).+1)%N.
Proof.
move => F_in_L; move: (F_in_L); move/vf_L_face: F_in_L; case/faceP => {}F F_sub_P F_in_L.
case: (ltnP 1 (dim F)) => [dim_gt1 | ?].
- rewrite ?dimN0_eq ?vf_prop0 ?vf_L_prop0 //.
  apply/congr1; rewrite vf_eq //=.
  rewrite span_fsetU span_fset1 addvC dim_add_line ?subnSK //=.
  + by rewrite dimN0_eq ?ltnS ?subn_gt0 ?vf_L_prop0 in dim_gt1.
  + rewrite -in_span_activeP ?vf_L_prop0 //.
    apply/poly_lePn; exists v; first by rewrite vf_L_v_in.
    by move: sep_v; apply/contraNN/poly_leP/hp_subset_hs.
- by rewrite [pval _]vf_dim1 // dim_pt vf_slice_pt dim0.
Qed.

End VertexFigurePolyBase.
End VertexFigurePolyBase.

Section VertexFigure.

Context {R : realFieldType} {n : nat}.

Lemma slice_polyI (e : lrel[R]_n) : {morph slice e : P Q / P `&` Q}.
Proof. move=> P Q; by rewrite RT.meetACA RT.meetxx. Qed.

Lemma vertex_figure (P : 'poly[R]_n) v :
  compact P -> v \in vertex_set P ->
  exists2 Q, compact Q &
  isof poly_preLattice [< [pt v]; P >]_(face_lattice P) (face_lattice Q).
Proof.
elim/polybW: P => base P P_compact v_vtx.
have v_face: [pt v] \in face_lattice P by rewrite -in_vertex_setP.
pose e := xchoose (conv_sep_hp (sep_vertex P_compact v_vtx)).
have hyp: vf_hyp P v e.
+ split=> //; exact: (xchooseP (conv_sep_hp (sep_vertex P_compact v_vtx))).
pose Φ := slice e; pose Q := Φ P; exists Q; rewrite ?compact_slice //.
set phi := slice e; exists phi; apply/meet_isof.
- exact: VertexFigurePolyBase.vf_inj.
- exact: VertexFigurePolyBase.vf_surj.
- move=> ????; exact: slice_polyI.
Qed.

(*Search _ face_lattice.
have slice_bij :
  {in [< [pt v]; P >]_(face_lattice P) & on (face_lattice Q), bijective (slice e)}.
+ apply/(inj_surj_bij _ _ _ _ _ _ (poly0_face _)). (* UGLY, FIX IT *)
  - by apply/VertexFigurePolyBase.vf_im.
  - by apply/VertexFigurePolyBase.vf_inj.
  - by apply/VertexFigurePolyBase.vf_surj.
have slice_morph:
  fmorphism [< [pt v]; P>]_(face_lattice P) (face_lattice Q) (slice e).
+ apply/meet_fmorphism => //.
  - by apply/VertexFigurePolyBase.vf_im.
  - by move=>??; rewrite slice_polyI.
exists (FMorphism slice_morph) => //.
Qed.*)

(*
Definition face_set_itv (P : 'poly[R]_n) F F' :=
  [fset Q in face_lattice P | F `<=` Q `<=` F']%fset.

Lemma face_set_itv_vtx (P : 'poly[R]_n) (v : 'cV[R]_n) :
  v \in vertex_set P ->
  [fset Q in face_lattice P | v \in Q]%fset = face_set_itv P ([pt v]) P.
Proof.
move=> vP; apply/fsetP=> /= x; apply/idP/idP.
+ case/imfsetP=> /= {}Q /andP[QP vQ] ->; apply/imfsetP => /=.
  exists Q => //=; rewrite !inE QP /= pt_subset vQ /=.
  by apply: face_subset.
+ case/imfsetP=> /= Q /andP[QP /andP[vQ _]] ->; apply/imfsetP => /=.
  by exists Q => //; rewrite !inE QP /=; rewrite -pt_subset.
Qed.

Lemma vf_im (P : 'compact[R]_n) v e F :
  vf_hyp P v e ->
    F \in face_set_itv P ([pt v]) P -> (slice e F) \in face_lattice (slice e P).
Proof.
case: P => [[]]; elim/polybW => base P ? P_compact /= hyp F_in.
by apply/(VertexFigurePolyBase.vf_im hyp); rewrite face_set_itv_vtx ?hyp.1.
Qed.

Lemma vf_inj (P : 'compact[R]_n) v e :
  vf_hyp P v e -> {in face_set_itv P ([pt v]) P &, injective (slice e)}.
Proof.
case: P => [[]]; elim/polybW => base P ? P_compact /= hyp Q Q' Q_in Q'_in ?.
by apply/(VertexFigurePolyBase.vf_inj P_compact hyp); rewrite ?face_set_itv_vtx ?hyp.1.
Qed.

Lemma vf_surj (P : 'compact[R]_n) v e F :
  vf_hyp P v e ->
  F \in face_lattice (slice e P) -> exists2 F', F' \in face_set_itv P ([pt v]) P & F = slice e F'.
Proof.
case: P => [[]]; elim/polybW => base P ? P_compact /= hyp.
move/(VertexFigurePolyBase.vf_surj P_compact hyp) => [F' F'_in eq_slice].
by exists F'; rewrite -?face_set_itv_vtx ?hyp.1.
Qed.

Lemma face_intervalE (P : 'pointed[R]_n) (F F' Q : face_lattice P) :
  (Q \in interval F F') = (val Q \in face_set_itv P (val F) (val F')).
Proof.
apply/intervalP/idP => [[le_FQ le_QF']|].
+ apply/imfsetP=> /=; exists (val Q) => //; rewrite !inE.
  by rewrite -!leEfaces le_FQ le_QF' (valP Q).
+ case/imfsetP=> /= Q' /andP[Q'P /andP[le_FQ' le_Q'F']] /esym Q'E.
  by rewrite !leEfaces /= -Q'E le_FQ' le_Q'F'.
Qed.

Lemma face_of_vtxP (P : 'poly[R]_n) (v : vertex_set P) :
  [pt (val v)] \in face_lattice P.
Proof.
by rewrite -in_vertex_setP (valP v).
Qed.

Definition face_of_vtx (P : 'poly[R]_n) (v : vertex_set P) :=
  [` face_of_vtxP v]%fset : face_lattice P.

Lemma vtx_of_atomP (P : 'pointed[R]_n) (F : face_lattice P) :
  atom F -> exists (v : vertex_set P), val F == [pt (val v)].
Proof.
by move/atom_faceP => [x x_in ->]; exists [` x_in]%fset.
Qed.

Definition vtx_of_atom (P : 'pointed[R]_n) (F : face_lattice P) (F_atom : atom F) :=
  xchoose (vtx_of_atomP F_atom).

Lemma vtx_of_atomE (P : 'pointed[R]_n) (F : face_lattice P) (F_atom : atom F) :
  [pt (val (vtx_of_atom F_atom))] = val F.
Proof.
rewrite /vtx_of_atom; set s := (X in xchoose X).
by case: (xchooseP s) => /eqP <-.
Qed.

 (*
Lemma face_of_vtxK (P : 'pointed[R]_n) :
  {in (@atom _ [finLatticeType of (face_lattice P)]),
      cancel (@vtx_of_atom P) (@face_of_vtx P) }.
 *)


Section LiftSlice.

Variable (P : 'compact[R]_n) (Fv : face_lattice P).
Hypothesis Fv_atom : atom Fv.
Let v := vtx_of_atom Fv_atom.
Let e := xchoose (conv_sep_hp (sep_vertex (valP P) (valP v))).

Local Lemma hyp : vf_hyp P (val v) e.
split; first apply/valP.
by apply: (xchooseP (conv_sep_hp (sep_vertex (valP P) (valP v)))).
Qed.

Lemma lift_sliceP (F : face_lattice P) :
  F \in interval Fv 1%O -> slice e (val F) \in face_lattice (slice e P).
Proof.
by rewrite face_intervalE /= => ?; apply/(vf_im hyp); rewrite vtx_of_atomE.
Qed.

Definition lift_slice (F : '[< Fv; 1%O >]) := [` lift_sliceP (valP F) ]%fset.

Lemma lift_slice_inj : injective lift_slice.
Proof.
move => F F' lift_eq.
apply/val_inj/val_inj/(vf_inj hyp) => //.
- by rewrite vtx_of_atomE; move: (valP F); rewrite face_intervalE /=.
- by rewrite vtx_of_atomE; move: (valP F'); rewrite face_intervalE /=.
- by move/(congr1 val): lift_eq.
Qed.

Lemma lift_slice_surj (F : face_lattice (slice e P)) : exists F', F = lift_slice F'.
Proof.
move: (vf_surj hyp (valP F)) => [F0].
rewrite !inE /= => /andP [F_face v_in F_eq].
rewrite vtx_of_atomE in v_in.
exists (insubd (0 : '[<Fv; 1>])%O [` F_face]%fset ).
by apply/val_inj => /=; rewrite F_eq /insubd insubT //=.
Qed.

End LiftSlice.

Lemma inj_surj_bij (T1 T2: finType) (f : T1 -> T2) :
  injective f -> (forall y, exists x, y = f x) -> bijective f.
Proof.
move => f_inj f_surj.
have f_surj': forall y, exists x, y == f x by move => y; move: (f_surj y) => [x ->]; exists x.
pose g y := xchoose (f_surj' y); exists g.
- by move => x; apply/f_inj/eqP; rewrite eq_sym (xchooseP (f_surj' (f x))).
- by move => y; apply/eqP; rewrite eq_sym (xchooseP (f_surj' y)).
Qed.

(*
Lemma fin_joinE (disp : unit) (L : finLatticeType disp) (x y : L) :
  (x `|` y = \meet_(z : L | (z >= x) && (z >= y)) z)%O.
Proof.
apply/le_anti/andP; split.
- by apply/meetsP => z; rewrite leUx.
- by apply/meets_inf; rewrite leUl leUr.
Qed.*)

Lemma inj_mono (disp : unit)  (L L' : latticeType disp) (f : L -> L') :
  injective f -> {morph f : x y / (x `&` y)%O >-> (x `&` y)%O} -> {mono f : x y / x <= y}%O.
Proof.
move => f_inj f_meet x y.
by rewrite !leEmeet -f_meet (inj_eq f_inj).
Qed.

(*
Lemma bij_on_bij (I J : Type) (f : I -> J) (P : pred J) :
  bijective f -> {on P, bijective f}.
Proof.
by move => [g fgK gfK]; exists g => ??; [ apply/fgK | apply/gfK ].*)

Lemma bij_omorphism (disp : unit) (L L' : finLatticeType disp) (f : L -> L') :
  bijective f -> {morph f : x y / (x `&` y)%O >-> (x `&` y)%O} -> omorphism f.
Proof.
case => g fgK gfK f_meet; split => //.
have f_mono := (inj_mono (can_inj fgK) f_meet).
move => x y; apply/le_anti/andP; split.
- by rewrite -[X in (_ <= X)%O]gfK f_mono leUx -!f_mono gfK leUl leUr.
- by rewrite leUx !f_mono leUl leUr.
Qed.

Lemma vertex_figure (P : 'compact[R]_n) (x : face_lattice P) : atom x ->
  exists Q : 'compact[R]_n,
  exists f : {omorphism '[< x; 1 >] -> face_lattice Q}%O, bijective f.
Proof.
move => x_atom.
pose v := vtx_of_atom x_atom.
pose e := xchoose (conv_sep_hp (sep_vertex (valP P) (valP v))).
pose Q := Compact (compact_slice P e); exists Q.
pose f := lift_slice x_atom.
have f_bij : bijective f.
- apply/inj_surj_bij; by [apply/lift_slice_inj | apply/lift_slice_surj].
have f_omorph : omorphism f.
- apply/bij_omorphism => //.
  move => y z; apply/val_inj => /=; rewrite -/e.
  by apply/poly_eqP => u; rewrite !inE andbACA andbb.
by exists (OMorphism f_omorph).
Qed.*)

End VertexFigure.

(* -------------------------------------------------------------------- *)
Local Open Scope order_scope.

Section ClosednessByInterval.
Context (R : realFieldType) (n : nat).

Lemma proper_pt (P : 'poly[R]_n) v : P `<` [pt v] -> P = [poly0].
Proof.
apply/contraTeq; case/poly_eq0Pn=> w w_in.
apply/contraT; rewrite negbK => P_lt.
have /poly_leP/(_ _ w_in): P `<=` [pt v] by apply/RT.ltW.
rewrite in_pt => /eqP w_eq_v.
move: P_lt; rewrite -w_eq_v.
by case/poly_properP => _ [z]; rewrite in_pt => /eqP ->; rewrite w_in.
Qed.

Lemma atom_face (P : 'pointed[R]_n) Q :
  reflect (exists2 v, v \in vertex_set P & Q = [pt v])
          (atom (face_lattice P) Q).
Proof.
apply/(iffP atomP); rewrite fbot_face_lattice.
- case=> Q_face Q_prop0 Q_min.
  have Q_pointed: pointed Q by apply/(pointedS (face_subset Q_face))/valP.
  case/fset0Pn: (vertex_setN0 Q_prop0 Q_pointed)=> v v_vtx_Q.
  have v_vtx_P: v \in vertex_set P by move: v_vtx_Q; apply/fsubsetP/vertex_setS.
  exists v => //.
  have v_in: [pt v] `<=` Q by rewrite pt_subset vertex_set_subset.
  apply/(RT.le_anti [leo:<=%P])/andP; split=> //.
  rewrite RT.comparable_leNgt ?RT.ge_comparable //.
  by apply/Q_min; by rewrite -?in_vertex_setP ?pt_proper0.
- case=> v v_vtx ->; split; rewrite -?in_vertex_setP ?pt_proper0 //.
  move=> Q' _; apply/contraL.
  by move/proper_pt ->; rewrite RT.ltxx.
Qed.

(*Lemma codomfE (T : choiceType) (L : {preLattice T})
      (S : {finLattice L}) (f : {fmorphism S on L}) :
  \codomf = f @` (S : {fset _}) :> {fset _}.
Admitted.*)

(* Lemma closed_by_interval (P : 'pointed[R]_n) x y :
  compact P -> x \in face_lattice P -> y \in face_lattice P -> x `<=` y ->
  exists2 Q : 'pointed[R]_n, compact Q
             & isof poly_preLattice [< x; y >]_(face_lattice P) (face_lattice Q).
(*& rank y = (dim Q + rank x)%N*)
Proof.
move => P_compact x_in y_in x_le_y.
pose Pt (S : {finLattice poly_preLattice}) :=
  exists2 Q : 'pointed[R]_n, compact Q & isof poly_preLattice S (face_lattice Q).
suff h_Pt : forall (S : {finLattice poly_preLattice}) x y,
  x \in S -> y \in S -> x `<=` y ->
  Pt S -> Pt [< x; y >]_S.
- apply/h_Pt => //; exists P => //; exact: isof_refl.
- apply/(ind_id (P := Pt)). (* FIX IT *)
  + move=> S z z_atom [Q] Q_compact /isofP [f] [f_morph f_inj f_surj].
    have /atom_face [v v_vtx fz_v]: atom (face_lattice Q) (f z).
      by rewrite fmorph_atom //; apply/misof_fmorph. (* TODO: fix *)
    case: (vertex_figure Q_compact v_vtx) => Q' Q'_compact Q'_iso.
    exists (Pointed (compact_pointed Q'_compact)) => //. (* TODO: fix it *)
    apply/isof_trans: Q'_iso; exists f.
    suff ->: [< [pt v]; Q >]_(face_lattice Q) =
      f @` ([< z; \ftop_S >]_S : {fset _}) :> {fset _}.
    * apply/(itv_isomorph (S2 := (face_lattice Q))); (* TODO: fix it *)
        rewrite ?lef1 ?mem_ftop ?mem_atom //.
      by apply/misof_fmorph. (* TODO: fix it *)
    * rewrite -fz_v fmorph_itv ?lef1 ?mem_ftop ?mem_atom //.
      rewrite fmorph1.
      have ->: \codom f = face_lattice Q by apply/val_inj=> //. (* TODO: fix it *)
      by rewrite ftop_face_lattice.
  + move=> S z coatom_z [Q] Q_compact /isofP [f f_surj f_inj].
    pose Q' := f z.
    have Q'_face: Q' \in face_lattice Q
      by rewrite inE -f_surj in_imfset ?mem_coatom.
    have Q'_compact : compact Q'
      by apply/face_compact: Q'_face.
    exists (Pointed (compact_pointed Q'_compact)) => //. (* TODO: fix it *)
    exists f.
    suff ->: face_lattice Q' = f @` ([< \fbot_S; z >]_S : {fset _}) :> {fset _}.
    * apply/(itv_isomorph (S2 := face_lattice Q));
        rewrite ?le0f ?mem_fbot ?mem_coatom //.
      by apply/misof_fmorph. (* TODO: fix it *)
    * rewrite fmorph_itv ?le0f ?mem_fbot ?mem_coatom //.
      rewrite fmorph0.
      have ->: \codom f = face_lattice Q by apply/val_inj=> //. (* TODO: fix it *)
      by rewrite fbot_face_lattice -face_lattice_of_face.
Qed. *)

(*
Lemma closed_by_interval_r (x : face_lattice P) :
   exists Q : 'compact[R]_n,
   exists2 f : {omorphism '[< x; 1 >] -> face_lattice Q},
     bijective f & dim P = (dim Q + rank x)%N.
Proof.
elim/rank_ind: x => /= x; case: (x =P 0) => [-> _|/eqP nz_x ih].
+ pose h := omorph_full_intv_val [tbLatticeType of face_lattice P].
  exists P, (TBOMorphism h); first by apply: bij_full_intv_val.
  by rewrite rank0 addn0.
case: (graded_rankS (x := x)); first by rewrite rank_gt0 lt0x.
move=> y lt_y_x /esym rkxE; case: (ih y _); first by rewrite rkxE.
move=> Q [f bij_f rkPE]; set I := '[< f x%:I; 1 >].
case: (@vertex_figure R n Q (f x%:I)).
+ rewrite atomE rank_morph_bij //; last by case: {+}f.
  by rewrite intv_rankE /= rkxE subSn // subnn.
move=> T [g bij_g]; exists T.
set h : _ -> face_lattice Q := fun (z : '[<x; 1>]) => f (z%:I_[< <~ y ; >]).
have hcodom z : h z \in interval (f x%:I) 1.
+ rewrite intervalE lex1 andbT /h; apply: omorph_homo.
  by rewrite leEsub /= (intervalPL (valP z)).
pose k (z : '[<x; 1>]) : face_lattice T := g (Interval (hcodom z)).
have morph_k: omorphism k; first apply/omorphismP=> z1 z2.
+ rewrite -omorphI; congr (g _); apply: val_inj => /=.
  by rewrite /h /= -omorphI; congr (f _); apply/val_inj.
+ rewrite -omorphU; congr (g _); apply: val_inj => /=.
  by rewrite /h /= -omorphU; congr (f _); apply/val_inj.
+ have bij_k: bijective k.
  apply: bij_comp => //; case: (bij_f) => fI fK Kf.
  set hI := fun (z : '[<f x%:I; 1>]) => fI (val z).
  have hcodomI z : val (hI z) \in interval x 1.
  * rewrite intervalE lex1 andbT /hI.
    apply: (le_trans (y := (val x%:I_[< y; 1 >]))) => //.
    rewrite -leEsub -(omorph_mono (bij_inj bij_f)).
    by rewrite Kf (intervalPL (valP z)).
  exists (fun z => Interval (hcodomI z)).
  * by move=> z; apply: val_inj => /=; rewrite /hI /h /= fK.
  * case=> /= [z hz] /=; apply: val_inj; rewrite /h /=.
    rewrite [X in f X](_ : _ = hI (Interval hz)) ?Kf //=.
    by apply: val_inj.
exists (OMorphism morph_k) => //=; rewrite rkxE -addSnnS.
have ->: dim T = rank (k 1).
+ set ok := bij_omorphism_tbomorphism bij_k morph_k.
  by have /= -> := omorph1 (TBOMorphism ok).
rewrite rank_morph_bij // {1}/rank /= /vrank /=.
by rewrite addSnnS -rkxE subnK //; apply/le_homo_rank/lex1.
Qed.

Lemma closed_by_interval (x y : face_lattice P) : (x <= y)%O ->
   exists Q : 'compact[R]_n,
   exists2 f : {omorphism '[< x; y >] -> face_lattice Q},
     bijective f & rank y = (dim Q + rank x)%N.
Proof.
case: (closed_by_interval_r x) => Q [f bij_f dimPE] le_xy.
set I : face_lattice Q := f y%:I; have cI: compact (val I).
+ by apply/(face_compact (valP Q))/valP.
have gI (z : '[<x; y>]) : val (f z%:I_[< ; 1%O ~> >]) \in face_lattice (val I).
+ rewrite (face_set_of_face (valP (f y%:I))).
  set zc := _%:I_[< ; 1 ~> >]; have le_zy: zc <= y%:I.
  - by rewrite leEsub /= (intervalPR (valP z)).
  rewrite 2!inE /=; apply/andP; split; first by apply: valP.
  by have := omorph_homo f le_zy; rewrite leEfaces.
pose g (z : '[<x; y>]) := [` gI z]%fset.
+ have bij_g: bijective g.
  case: bij_f => /= fI fK Kf.
  have hgK (z : face_lattice (val I)) : val z \in face_lattice Q.
  * by have /fsubsetP := face_setS (valP I); apply; apply/valP.
  pose gK (z : face_lattice (val I)) := fI [` hgK z ]%fset.
  have h z: x <= val (gK z) <= y.
  * rewrite (intervalPL (valP _)) /gK /=.
    set qy := y%:I_[< x; 1 >]; suff: fI [`hgK z]%fset <= qy by [].
    rewrite -(omorph_mono (can_inj fK)) Kf leEfaces /qy /=.
    by apply: face_subset.
  exists (fun z => Interval (h z)).
  * case=> z hz /=; rewrite /gK /=; apply: val_inj=> /=.
    set c := (X in fI {| fsval := fsval X |}).
    rewrite [X in fI X](_ : _ = c) //; first by rewrite /c fK.
    by apply: val_inj.
  * case=> /= z hz /=; apply: val_inj; rewrite /g /=.
    rewrite [_%:I_[< ; 1 ~> >]](_ : _ = gK [`hz]%fset).
    - by rewrite Kf. - by apply: val_inj.
have morph_g: omorphism g.
+ apply/bij_omorphism => // z1 z2; rewrite /g /=.
  by apply: val_inj => /=; rewrite widdenRI omorphI.
exists (Compact cI), (OMorphism morph_g) => //=.
pose J : 'pointed[R]_n := Pointed (compact_pointed cI).
pose JL := [gradedFinLatticeType of face_lattice J].
have ->: dim (fsval I) = rank (g 1 : JL).
+ set og := bij_omorphism_tbomorphism bij_g morph_g.
  by have /= -> := omorph1 (TBOMorphism og).
rewrite rank_morph_bij // {2}/rank /= /vrank /=.
by rewrite subnK //; apply/le_homo_rank.
Qed.*)
End ClosednessByInterval.

(* -------------------------------------------------------------------- *)
Global Instance expose_lexx (disp : unit) (L : porderType disp) (x : L) :
  expose (x <= x)%O := Expose (lexx x).

(*
Section Diamond.
Context {T : choiceType} {L : {preLattice T}}.

Implicit Type (S : {finLattice L}).

Definition is_diamond S :=
  [exists x, [exists y, [&& (S == [fset z in [:: x; y; \fbot_S; \ftop_S]], ~~ (x <=_L y) & ~~ (y <=_L x)]]].

                                              x \in S

*)
(* -------------------------------------------------------------------- *)
(*Section DiamondProperty.

Context (R : realFieldType) (n : nat) (P : 'compact[R]_n).

Lemma diamond x y :
  x \in face_lattice P -> y \in face_lattice Q ->
    x `<=` y -> dim y = (dim x).+2 ->
    exists z1 z2, : face_lattice P,
  [/\ z1 \in face_lattice P,


   forall z : '[<x; y>], val z \in [:: x; y; z1; z2]
      , rank z1 = (rank x).+1
      , rank z2 = (rank x).+1
      , x <= z1 <= y & x <= z2 <= y].
Proof.
move=> rkyE le_xy; case: (closed_by_interval le_xy)=> [Q] [f bij_f].
rewrite {}rkyE -addn2 addnC => /addIn /esym.
case/dim2P => [|/= z1 [z2] QE ne_z]; first by case: {+}Q.
have hz1: [pt z1] \in face_lattice Q.
+ by rewrite QE face_set_segm !inE eqxx !(orbT, orTb).
have hz2: [pt z2] \in face_lattice Q.
+ by rewrite QE face_set_segm !inE eqxx !(orbT, orTb).
case: (bij_f) => /= fI fK Kf.
pose y1 := fI [` hz1]%fset; pose y2 := fI [` hz2]%fset.
exists (val y1), (val y2); split; first move=> z.
+ rewrite [in X in _ \in [:: X, _ & _]](_ : x = val x%:I_[< x; y >]) //.
  rewrite [in X in _ \in [:: _, X & _]](_ : y = val y%:I_[< x; y >]) //.
  set s := [:: x%:I; y%:I; y1; y2]; set s' := (X in _ \in X).
  have ->: s' = map val s by [].
  rewrite {s'}/s; rewrite mem_map; last by apply: val_inj.
  rewrite -(mem_map (f := val \o f)); last first.
  * by apply/inj_comp; [apply/val_inj | apply/(can_inj fK)].
  have /= := valP (f z); rewrite [in X in _ \in X -> _]QE.
  rewrite face_set_segm ![in X in X -> _]inE -!orbA.
  rewrite mem_seq4 -[X in _ -> X](rwP or4P) => /or4P[] /eqP->.
  * constructor 1; have ->: x%:I_[<x; y>] = 0 by apply: val_inj.
    case: {+}f bij_f => /= g morph_g bij_g.
    set h := bij_omorphism_tbomorphism bij_g morph_g.
    by have /= -> := (omorph0 (TBOMorphism h)).
  * by constructor 3; rewrite Kf.
  * by constructor 4; rewrite Kf.
  * constructor 2; have ->: y%:I_[<x; y>] = 1 by apply: val_inj.
    case: {+}f bij_f => /= g morph_g bij_g.
    set h := bij_omorphism_tbomorphism bij_g morph_g.
    by have /= -> := (omorph1 (TBOMorphism h)); rewrite -QE.
+ have: rank y1 = (rank x%:I_[<x; y>]).+1; last first.
  * rewrite {1 2}/rank /= /vrank /= subnn -[in X in _ -> X]addn1 => <-.
    rewrite subnKC //; apply/le_homo_rank/(intervalPL (valP y1)).
  rewrite (_ : x%:I = 0) ?rank0 /y1; last by apply: val_inj.
  (rewrite rank_morph_bij; last by exists f); last first.
  * by apply: (inv_is_omorphism fK Kf); case: {+}(f).
  by rewrite /rank /= dim_pt.
+ have: rank y2 = (rank x%:I_[<x; y>]).+1; last first.
  * rewrite {1 2}/rank /= /vrank /= subnn -[in X in _ -> X]addn1 => <-.
    rewrite subnKC //; apply/le_homo_rank/(intervalPL (valP y2)).
  rewrite (_ : x%:I = 0) ?rank0 /y1; last by apply: val_inj.
  (rewrite rank_morph_bij; last by exists f); last first.
  * by apply: (inv_is_omorphism fK Kf); case: {+}(f).
  by rewrite /rank /= dim_pt.
+ by apply: (valP y1).
+ by apply: (valP y2).
Qed.
End DiamondProperty.
*)
