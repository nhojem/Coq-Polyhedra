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
Reserved Notation "'lrel' [ R ]_ n"
  (at level 8, format "'lrel' [ R ]_ n").

Reserved Notation "'lrel'"
  (at level 8).

Reserved Notation "'base_t' [ R , n ]"
  (at level 8, format "'base_t' [ R , n ]").

Reserved Notation "'base_t'"
  (at level 8).

Reserved Notation "[< A , b >]"
  (at level 8, format "[< A ,  b >]").

(* -------------------------------------------------------------------- *)
Section Base.
Context {R : Type} (n : nat).

Variant base_elt_type : predArgType := BaseElt of ('cV[R]_n * R).

Coercion base_elt_val b := let: BaseElt b := b in b.

Canonical base_elt_subType := Eval hnf in [newType for base_elt_val].
End Base.

Notation "'lrel' [ R ]_ n" := (@base_elt_type R n).
Notation "'lrel'" := (lrel[_]_(_)).
Notation "'base_t' [ R , n ]" := {fset lrel[R]_n}.
Notation "'base_t'" := (base_t[_,_]).
Notation "[< A , b >]" := (BaseElt (A, b)).

(* -------------------------------------------------------------------- *)
Definition be_eqMixin (R : eqType) n :=
  Eval hnf in [eqMixin of lrel[R]_n by <:].
Canonical be_eqType (R : eqType) n:=
  Eval hnf in EqType lrel[R]_n  (be_eqMixin R n).
Definition be_choiceMixin (R : choiceType) n :=
  [choiceMixin of lrel[R]_n by <:].
Canonical be_choiceType (R : choiceType) n :=
  Eval hnf in ChoiceType lrel[R]_n (be_choiceMixin R n).
Definition be_countMixin (R : countType) n :=
  [countMixin of lrel[R]_n by <:].
Canonical be_countType (R : countType) n :=
  Eval hnf in CountType lrel[R]_n (be_countMixin R n).
Canonical be_subCountType (R : countType) n :=
  Eval hnf in [subCountType of lrel[R]_n].
Definition be_finMixin (R : finType) n :=
  [finMixin of lrel[R]_n by <:].
Canonical be_finType (R : finType) n :=
  Eval hnf in FinType lrel[R]_n (be_finMixin R n).
Canonical be_subFinType (R : finType) n :=
  Eval hnf in [subFinType of lrel[R]_n].

(* -------------------------------------------------------------------- *)
Section BaseTheory.
Context (R : Type) (n : nat).

Lemma beW (P : lrel[R]_n -> Prop) :
  (forall A b, P [<A, b>]) -> (forall b, P b).
Proof. by move=> ih [[]]. Qed.

Lemma beE (b : lrel[R]_n) : [<b.1, b.2>] = b.
Proof. by elim/beW: b. Qed.
End BaseTheory.

Lemma be_eqE (R : eqType) n (b1 b2 : lrel[R]_n) :
  (b1 == b2) = [&& b1.1 == b2.1 & b1.2 == b2.2].
Proof. by []. Qed.

Lemma be_eqP (R : eqType) n (b1 b2 : lrel[R]_n) :
  reflect (b1.1 = b2.1 /\ b1.2 = b2.2) (b1 == b2).
Proof.
rewrite be_eqE; apply: (iffP andP).
+ by case=> [/eqP-> /eqP->]. + by case=> -> ->.
Qed.

(* -------------------------------------------------------------------- *)
Section BaseEncoding.
Context {R : eqType} (n : nat).

Definition base_elt_to_col (v : lrel[R]_n) : 'cV[R]_(n+1) :=
  col_mx v.1 (const_mx v.2).

Definition col_to_base_elt (v : 'cV[R]_(n+1)) : lrel[R]_n :=
  [< usubmx v, dsubmx v 0 0 >].

Lemma base_elt_to_colK : cancel col_to_base_elt base_elt_to_col.
Proof.
move=> c; apply/colP=> i; rewrite mxE.
by case: splitP' => j -> /=; rewrite !mxE ?ord1.
Qed.

Lemma col_to_base_eltK : cancel base_elt_to_col col_to_base_elt.
Proof.
elim/beW=> A b; apply/eqP/be_eqP=> /=; split.
+ by apply/colP=> i; rewrite mxE col_mxEu.
+ by rewrite mxE col_mxEd mxE.
Qed.
End BaseEncoding.

(* -------------------------------------------------------------------- *)
Section BaseEncodingTheory.
Context {R : realFieldType} (n m : nat).

Lemma base_elt_to_colM (A : 'M[R]_(n, m)) (b : 'cV[R]_n) (x : 'cV[R]_n) :
  base_elt_to_col [< A^T *m x, '[b, x] >] = (row_mx A b)^T *m x.
Proof.
apply/colP=> i; rewrite ![in X in X = _]mxE /=; case: splitP'.
+ by move=> j ->; rewrite tr_row_mx mul_col_mx col_mxEu.
+ move=> j ->; rewrite ord1 tr_row_mx mul_col_mx col_mxEd.
  by rewrite mxE -vdot_def mxE eqxx mulr1n vdotC.
Qed.
End BaseEncodingTheory.

(* -------------------------------------------------------------------- *)
Section BaseZmod.
Context {R : zmodType} {n : nat}.

Implicit Types (b : lrel[R]_n).

Definition be0         := [< (0 : 'cV[R]_n), (0 : R) >].
Definition beadd b1 b2 := [< b1.1 + b2.1, b1.2 + b2.2 >].
Definition beopp b     := [< -b.1, -b.2 >].

Lemma be_zmod_mixin :
  [/\ associative beadd
    , commutative beadd
    , left_id be0 beadd
    & left_inverse be0 beopp beadd].
Proof. split.
+ by move=> b1 b2 b3; rewrite /beadd 2!addrA.
+ by move=> b1 b2; rewrite /beadd [b2.1 + _]addrC [b2.2 + _]addrC.
+ by move=> b; rewrite /beadd 2!add0r beE.
+ by move=> b; rewrite /beadd 2!addNr.
Qed.

Let beaddA  := let: And4 h _ _ _ := be_zmod_mixin in h.
Let beaddC  := let: And4 _ h _ _ := be_zmod_mixin in h.
Let beadd0r := let: And4 _ _ h _ := be_zmod_mixin in h.
Let beaddNr := let: And4 _ _ _ h := be_zmod_mixin in h.

Definition be_zmodMixin := ZmodMixin beaddA beaddC beadd0r beaddNr.
Canonical be_zmodType := Eval hnf in ZmodType lrel be_zmodMixin.

Lemma beaddE b1 b2 : b1 + b2 = [< b1.1 + b2.1, b1.2 + b2.2 >].
Proof. by []. Qed.

Lemma beoppE b : -b = [< -b.1, -b.2 >].
Proof. by []. Qed.
End BaseZmod.

(* -------------------------------------------------------------------- *)
Section BaseEltEncodingZmodMorph.
Context {R : zmodType} {n : nat}.

Lemma base_elt_to_col_is_additive : additive (@base_elt_to_col R n).
Proof.
move=> /= b1 b2; apply/colP=> i; rewrite !mxE.
by case: splitP'=> j _; rewrite !mxE.
Qed.

Canonical base_elt_to_col_additive := Additive base_elt_to_col_is_additive.
End BaseEltEncodingZmodMorph.

(* -------------------------------------------------------------------- *)
Section BaseLmod.
Context {R : ringType} {n : nat}.

Implicit Types (b : lrel[R]_n).

Definition bescale c b := [< c *: b.1, c * b.2 >].

Lemma be_lmod_mixin :
  [/\ forall c1 c2 b, bescale c1 (bescale c2 b) = bescale (c1 * c2) b
    , left_id 1 bescale
    , right_distributive bescale +%R
    & forall b, {morph bescale^~ b : x y / x + y}].
Proof. split.
+ by move=> c1 c2 b; rewrite /bescale scalerA mulrA.
+ by move=> b; rewrite /bescale scale1r mul1r beE.
+ by move=> c b1 b2; rewrite /bescale scalerDr !beaddE mulrDr.
+ by move=> b c1 c2; rewrite /bescale beaddE scalerDl mulrDl.
Qed.

Let bescaleA  := let: And4 h _ _ _ := be_lmod_mixin in h.
Let bescale1  := let: And4 _ h _ _ := be_lmod_mixin in h.
Let bescaleDr := let: And4 _ _ h _ := be_lmod_mixin in h.
Let bescaleDl := let: And4 _ _ _ h := be_lmod_mixin in h.

Definition be_lmodMixin := LmodMixin bescaleA bescale1 bescaleDr bescaleDl.
Canonical be_lmodType := Eval hnf in LmodType R lrel be_lmodMixin.

Lemma bescaleE c b : c *: b = [< c *: b.1, c * b.2 >].
Proof. by []. Qed.
End BaseLmod.

(* -------------------------------------------------------------------- *)
Section BaseEltEncodingLmodMorph.
Context {R : ringType} {n : nat}.

Lemma base_elt_to_col_is_scalable : scalable (@base_elt_to_col R n).
Proof.
move=> c b /=; apply/colP=> i; rewrite !mxE.
by case: splitP'=> j _; rewrite !mxE.
Qed.

Canonical base_elt_to_col_scalable := AddLinear base_elt_to_col_is_scalable.
End BaseEltEncodingLmodMorph.

(* -------------------------------------------------------------------- *)
Section BaseMorph.
Context {R : zmodType} {n : nat}.

Implicit Types (b : lrel[R]_n).

Lemma beadd_p1E b1 b2 : (b1 + b2).1 = b1.1 + b2.1.
Proof. by []. Qed.

Lemma beadd_p2E b1 b2 : (b1 + b2).2 = b1.2 + b2.2.
Proof. by []. Qed.
End BaseMorph.

(* -------------------------------------------------------------------- *)
Section BaseVect.
Context {R : fieldType} {n : nat}.

Fact be_vect_iso : Vector.axiom (n+1) lrel[R]_n.
  (* there should be a way to exploit the connection betwseen base_elt and 'cV[R]_n * R^o
   * for which there is a canonical vectType structure                                    *)
Proof.
pose f (e : lrel[R]_n) := (col_mx e.1 (e.2%:M))^T.
exists f.
- move => ???; by rewrite /f raddfD /= -add_col_mx linearD /= -scale_scalar_mx -scale_col_mx linearZ.
- pose g (x : 'rV_(n+1)) := [< (lsubmx x)^T, (rsubmx x) 0 0 >] : (lrel[R]_n).
  exists g; move => x.
  + apply/eqP/be_eqP; split; rewrite /f /=.
    * by rewrite tr_col_mx row_mxKl trmxK.
    * by rewrite tr_col_mx row_mxKr tr_scalar_mx /= mxE mulr1n.
  + apply/rowP => i; case: (splitP' i) => [i' ->| i' ->].
    * by rewrite /f mxE col_mxEu !mxE.
    * by rewrite /f mxE col_mxEd mxE [i']ord1_eq0 mulr1n /= mxE.
Qed.
Definition be_vectMixin := VectMixin be_vect_iso.
Canonical be_vectType := VectType R lrel[R]_n be_vectMixin.

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

Definition befst := linfun (Linear fst_lmorph).

End BaseVect.

(* -------------------------------------------------------------------- *)
Section Combine.
Context {R : realFieldType} {n : nat} (base : base_t[R,n]).

Implicit Types (w : {fsfun lrel[R]_n ~> R}).

Lemma combineb1E w : (finsupp w `<=` base)%fset ->
  (combine w).1 = \sum_(v : base) w (val v) *: (val v).1.
Proof.
move=> le_wb; rewrite (combinewE le_wb).
by apply (big_morph (fst \o val) beadd_p1E).
Qed.

Lemma combineb2E w : (finsupp w `<=` base)%fset ->
  (combine w).2 = \sum_(v : base) w (val v) * (val v).2.
Proof.
move=> le_wb; rewrite (combinewE le_wb).
by apply (big_morph (snd \o val) beadd_p2E). Qed.

Definition combinebE w (h : (finsupp w `<=` base)%fset) :=
  (@combineb1E w h, @combineb2E w h).
End Combine.
