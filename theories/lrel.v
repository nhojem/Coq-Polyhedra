(* --------------------------------------------------------------------
 * Copyright (c) - 2017--2020 - Xavier Allamigeon <xavier.allamigeon at inria.fr>
 * Copyright (c) - 2017--2020 - Ricardo D. Katz <katz@cifasis-conicet.gov.ar>
 * Copyright (c) - 2019--2020 - Pierre-Yves Strub <pierre-yves@strub.nu>
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect all_algebra finmap.
Require Import extra_misc inner_product row_submx barycenter vector_order.

Import Order.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GRing.Theory Num.Theory.

(* -------------------------------------------------------------------- *)
Reserved Notation "R '.-lrel[' T ]_ n"
  (at level 8, format "R '.-lrel[' T ]_ n").

Reserved Notation "'lrel[' R ]_ n"
  (at level 8, format "'lrel[' R ]_ n").

Reserved Notation "'lrel_' n"
  (at level 8).

Reserved Notation "R '.-base_t[' T , n ]"
  (at level 8, format "R '.-base_t[' T , n ]").

Reserved Notation "'base_t[' R , n ]"
  (at level 8, format "'base_t[' R , n ]").

Reserved Notation "'base_t'"
  (at level 8).

Reserved Notation "[< A , b >]"
  (at level 8, format "[< A ,  b >]").

(* -------------------------------------------------------------------- *)
Section Base.
Context {R T : Type} (n : nat).

Variant lrel_type : predArgType := LRel of ('cV[R]_n * T).

Coercion lrel_val b := let: LRel b := b in b.

Canonical lrel_subType := Eval hnf in [newType for lrel_val].
End Base.

Notation "R '.-lrel['  T ]_ n" := (@lrel_type R T n).
Notation "'lrel[' R ]_ n" := (R.-lrel[R^o]_n).
Notation "'lrel_' n" := (lrel[_]_n).
Notation "R '.-base_t[' T , n ]" := {fset R.-lrel[T]_n}.
Notation "'base_t[' R , n ]" := (R.-base_t[R^o,n]).
Notation "'base_t'" := (base_t[_,_]).
Notation "[< A , b >]" := (LRel (A, b)).

(* -------------------------------------------------------------------- *)
Definition lrel_eqMixin (R T : eqType) n :=
  Eval hnf in [eqMixin of R.-lrel[T]_n by <:].
Canonical lrel_eqType (R T : eqType) n:=
  Eval hnf in EqType R.-lrel[T]_n  (lrel_eqMixin R T n).
Definition lrel_choiceMixin (R T : choiceType) n :=
  [choiceMixin of R.-lrel[T]_n by <:].
Canonical lrel_choiceType (R T : choiceType) n :=
  Eval hnf in ChoiceType R.-lrel[T]_n (lrel_choiceMixin R T n).
Definition lrel_countMixin (R T : countType) n :=
  [countMixin of R.-lrel[T]_n by <:].
Canonical lrel_countType (R T : countType) n :=
  Eval hnf in CountType R.-lrel[T]_n (lrel_countMixin R T n).
Canonical lrel_subCountType (R T : countType) n :=
  Eval hnf in [subCountType of R.-lrel[T]_n].
Definition lrel_finMixin (R T : finType) n :=
  [finMixin of R.-lrel[T]_n by <:].
Canonical lrel_finType (R T : finType) n :=
  Eval hnf in FinType R.-lrel[T]_n (lrel_finMixin R T n).
Canonical lrel_subFinType (R T : finType) n :=
  Eval hnf in [subFinType of R.-lrel[T]_n].

(* -------------------------------------------------------------------- *)
Section BaseTheory.
Context (R T : Type) (n : nat).

Lemma lrelW (P : R.-lrel[T]_n -> Prop) :
  (forall A b, P [<A, b>]) -> (forall b, P b).
Proof. by move=> ih [[]]. Qed.

Lemma lrelE (b : R.-lrel[T]_n) : [<b.1, b.2>] = b.
Proof. by elim/lrelW: b. Qed.
End BaseTheory.

Lemma lrel_eqE (R T : eqType) n (b1 b2 : R.-lrel[T]_n) :
  (b1 == b2) = [&& b1.1 == b2.1 & b1.2 == b2.2].
Proof. by []. Qed.

Lemma lrel_eqP (R T : eqType) n (b1 b2 : R.-lrel[T]_n) :
  reflect (b1.1 = b2.1 /\ b1.2 = b2.2) (b1 == b2).
Proof.
rewrite lrel_eqE; apply: (iffP andP).
+ by case=> [/eqP-> /eqP->]. + by case=> -> ->.
Qed.

(* -------------------------------------------------------------------- *)
Section BaseEncoding.
Context {R : eqType} (n : nat).

Definition lrel_to_col (v : lrel[R]_n) : 'cV[R]_(n+1) :=
  col_mx v.1 (const_mx v.2).

Definition col_to_lrel (v : 'cV[R]_(n+1)) : lrel[R]_n :=
  [< usubmx v, dsubmx v 0 0 >].

Lemma lrel_to_colK : cancel col_to_lrel lrel_to_col.
Proof.
move=> c; apply/colP=> i; rewrite mxE.
by case: splitP' => j -> /=; rewrite !mxE ?ord1.
Qed.

Lemma col_to_lrelK : cancel lrel_to_col col_to_lrel.
Proof.
elim/lrelW=> A b; apply/eqP/lrel_eqP=> /=; split.
+ by apply/colP=> i; rewrite mxE col_mxEu.
+ by rewrite mxE col_mxEd mxE.
Qed.
End BaseEncoding.

(* -------------------------------------------------------------------- *)
Section BaseEncodingTheory.
Context {R : realFieldType} (n m : nat).

Lemma lrel_to_colM (A : 'M[R]_(n, m)) (b : 'cV[R]_n) (x : 'cV[R]_n) :
  lrel_to_col [< A^T *m x, '[b, x] >] = (row_mx A b)^T *m x.
Proof.
apply/colP=> i; rewrite ![in X in X = _]mxE /=; case: splitP'.
+ by move=> j ->; rewrite tr_row_mx mul_col_mx col_mxEu.
+ move=> j ->; rewrite ord1 tr_row_mx mul_col_mx col_mxEd.
  by rewrite mxE -vdot_def mxE eqxx mulr1n vdotC.
Qed.
End BaseEncodingTheory.

(* -------------------------------------------------------------------- *)
Section BaseZmod.
Context {R T : zmodType} {n : nat}.

Implicit Types (b : R.-lrel[T]_n).

Definition lrel0         := [< (0 : 'cV[R]_n), (0 : T) >].
Definition lrel_add b1 b2 := [< b1.1 + b2.1, b1.2 + b2.2 >].
Definition lrel_opp b     := [< -b.1, -b.2 >].

Lemma lrel_zmod_mixin :
  [/\ associative lrel_add
    , commutative lrel_add
    , left_id lrel0 lrel_add
    & left_inverse lrel0 lrel_opp lrel_add].
Proof. split.
+ by move=> b1 b2 b3; rewrite /lrel_add 2!addrA.
+ by move=> b1 b2; rewrite /lrel_add [b2.1 + _]addrC [b2.2 + _]addrC.
+ by move=> b; rewrite /lrel_add 2!add0r lrelE.
+ by move=> b; rewrite /lrel_add 2!addNr.
Qed.

Let lrel_addA  := let: And4 h _ _ _ := lrel_zmod_mixin in h.
Let lrel_addC  := let: And4 _ h _ _ := lrel_zmod_mixin in h.
Let lrel_add0r := let: And4 _ _ h _ := lrel_zmod_mixin in h.
Let lrel_addNr := let: And4 _ _ _ h := lrel_zmod_mixin in h.

Definition lrel_zmodMixin := ZmodMixin lrel_addA lrel_addC lrel_add0r lrel_addNr.
Canonical lrel_zmodType := Eval hnf in ZmodType R.-lrel[T]_n lrel_zmodMixin.

Lemma lrel_addE b1 b2 : b1 + b2 = [< b1.1 + b2.1, b1.2 + b2.2 >].
Proof. by []. Qed.

Lemma lrel_oppE b : -b = [< -b.1, -b.2 >].
Proof. by []. Qed.
End BaseZmod.

(* -------------------------------------------------------------------- *)
Section LRelEncodingZmodMorph.
Context {R : zmodType} {n : nat}.

Lemma lrel_to_col_is_additive : additive (@lrel_to_col R n).
Proof.
move=> /= b1 b2; apply/colP=> i; rewrite !mxE.
by case: splitP'=> j _; rewrite !mxE.
Qed.

Canonical lrel_to_col_additive := Additive lrel_to_col_is_additive.
End LRelEncodingZmodMorph.

(* -------------------------------------------------------------------- *)
Section BaseLmod.
Context {R : ringType} {T : lmodType R} {n : nat}.

Implicit Types (b : R.-lrel[T]_n).

Definition lrel_scale c b := [< c *: b.1, c *: b.2 >].

Lemma lrel_lmod_mixin :
  [/\ forall c1 c2 b, lrel_scale c1 (lrel_scale c2 b) = lrel_scale (c1 * c2) b
    , left_id 1 lrel_scale
    , right_distributive lrel_scale +%R
    & forall b, {morph lrel_scale^~ b : x y / x + y}].
Proof. split.
+ by move=> c1 c2 b; rewrite /lrel_scale !scalerA.
+ by move=> b; rewrite /lrel_scale !scale1r lrelE.
+ by move=> c b1 b2; rewrite /lrel_scale !scalerDr !lrel_addE.
+ by move=> b c1 c2; rewrite /lrel_scale lrel_addE !scalerDl.
Qed.

Let lrel_scaleA  := let: And4 h _ _ _ := lrel_lmod_mixin in h.
Let lrel_scale1  := let: And4 _ h _ _ := lrel_lmod_mixin in h.
Let lrel_scaleDr := let: And4 _ _ h _ := lrel_lmod_mixin in h.
Let lrel_scaleDl := let: And4 _ _ _ h := lrel_lmod_mixin in h.

Definition lrel_lmodMixin := LmodMixin lrel_scaleA lrel_scale1 lrel_scaleDr lrel_scaleDl.
Canonical lrel_lmodType := Eval hnf in LmodType R R.-lrel[T]_n lrel_lmodMixin.

Lemma lrel_scaleE c b : c *: b = [< c *: b.1, c *: b.2 >].
Proof. by []. Qed.
End BaseLmod.

Section Test.
Variable (R : ringType) (n : nat) (e : lrel[R]_n) (x : R).

Goal  (x *: e) = 0.
rewrite lrel_scaleE -mulr_algl.
Abort.
End Test.

(* -------------------------------------------------------------------- *)
Section LRelEncodingLmodMorph.
Context {R : ringType} {n : nat}.

Lemma lrel_to_col_is_scalable : scalable (@lrel_to_col R n).
Proof.
move=> c b /=; apply/colP=> i; rewrite !mxE.
by case: splitP'=> j _; rewrite !mxE.
Qed.

Canonical lrel_to_col_scalable := AddLinear lrel_to_col_is_scalable.
End LRelEncodingLmodMorph.

(* -------------------------------------------------------------------- *)
Section BaseMorph.
Context {R : zmodType} {n : nat}.

Implicit Types (b : lrel[R]_n).

Lemma lrel_add_p1E b1 b2 : (b1 + b2).1 = b1.1 + b2.1.
Proof. by []. Qed.

Lemma lrel_add_p2E b1 b2 : (b1 + b2).2 = b1.2 + b2.2.
Proof. by []. Qed.
End BaseMorph.

(* -------------------------------------------------------------------- *)
Section BaseVect.
Context {R : fieldType} {n : nat}.

Fact lrel_vect_iso : Vector.axiom (n+1) lrel[R]_n.
  (* there should be a way to exploit the connection betwseen lrel and 'cV[R]_n * R^o
   * for which there is a canonical vectType structure                                    *)
Proof.
pose f (e : lrel[R]_n) := (col_mx e.1 (e.2%:M))^T.
exists f.
- move => ???; by rewrite /f raddfD /= -add_col_mx linearD /= -scale_scalar_mx -scale_col_mx linearZ.
- pose g (x : 'rV_(n+1)) := [< (lsubmx x)^T, (rsubmx x) 0 0 >] : (lrel[R]_n).
  exists g; move => x.
  + apply/eqP/lrel_eqP; split; rewrite /f /=.
    * by rewrite tr_col_mx row_mxKl trmxK.
    * by rewrite tr_col_mx row_mxKr tr_scalar_mx /= mxE mulr1n.
  + apply/rowP => i; case: (splitP' i) => [i' ->| i' ->].
    * by rewrite /f mxE col_mxEu !mxE.
    * by rewrite /f mxE col_mxEd mxE [i']ord1_eq0 mulr1n /= mxE.
Qed.
Definition lrel_vectMixin := VectMixin lrel_vect_iso.
Canonical lrel_vectType := VectType R lrel[R]_n lrel_vectMixin.

Lemma base_vect_subset (I I' : base_t[R,n]) :
  (I `<=` I')%fset -> (<< I >> <= << I' >>)%VS.
Proof.
by move => ?; apply/sub_span/fsubsetP.
Qed.

Lemma span_fsetU (I J : base_t[R,n]) :
  (<< (I `|` J)%fset >> = << I >> + << J >>)%VS.
Proof.
rewrite -span_cat; apply/eq_span => x.
by rewrite inE mem_cat.
Qed.

Lemma span_fset1 (v : lrel[R]_n) :
  (<< [fset v]%fset >> = <[ v ]>)%VS.
Proof.
by rewrite -span_seq1; apply/eq_span => x; rewrite !inE.
Qed.

Lemma fst_lmorph : lmorphism (fst : lrel[R]_n -> 'cV_n).
by [].
Qed.

Definition lrel_fst := linfun (Linear fst_lmorph).

End BaseVect.

Notation "'\fst'" := lrel_fst.

(* -------------------------------------------------------------------- *)
Section Combine.
Context {R : realFieldType} {n : nat} (base : base_t[R,n]).

Implicit Types (w : {fsfun lrel[R]_n ~> R}).

Lemma combineb1E w : (finsupp w `<=` base)%fset ->
  (combine w).1 = \sum_(v : base) w (val v) *: (val v).1.
Proof.
move=> le_wb; rewrite (combinewE le_wb).
by apply: (big_morph (fst \o val) lrel_add_p1E).
Qed.

Lemma combineb2E w : (finsupp w `<=` base)%fset ->
  (combine w).2 = \sum_(v : base) w (val v) * (val v).2.
Proof.
move=> le_wb; rewrite (combinewE le_wb).
by apply: (big_morph (snd \o val) lrel_add_p2E). Qed.

Definition combinebE w (h : (finsupp w `<=` base)%fset) :=
  (@combineb1E w h, @combineb2E w h).
End Combine.
