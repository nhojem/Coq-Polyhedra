(* --------------------------------------------------------------------
 * Copyright (c) - 2017--2020 - Xavier Allamigeon <xavier.allamigeon at inria.fr>
 * Copyright (c) - 2017--2020 - Ricardo D. Katz <katz@cifasis-conicet.gov.ar>
 * Copyright (c) - 2019--2020 - Pierre-Yves Strub <pierre-yves@strub.nu>
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect all_algebra finmap.
Require Import extra_misc inner_product vector_order.

Import Order.Theory.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.

(* -------------------------------------------------------------------- *)
Reserved Notation "{ 'fsfun' T ~> R }"
  (at level 0, format "{ 'fsfun'  T  ~>  R }").

Reserved Notation "{ 'conic' T ~> R }"
  (at level 0, format "{ 'conic'  T  ~>  R }").

Reserved Notation "{ 'convex' T ~> R }"
  (at level 0, format "{ 'convex'  T  ~>  R }").

Reserved Notation "0 %:FS"
  (at level 2, format "0 %:FS").

Reserved Notation "0 %:PFS"
  (at level 1, format "0 %:PFS").

Reserved Notation "x \bary V"
  (at level 70, format "x  \bary  V").

(* -------------------------------------------------------------------- *)
Declare Scope conicfun_scope.
Declare Scope convexfun_scope.

(* -------------------------------------------------------------------- *)
Notation "{ 'fsfun' T ~> R }" := {fsfun T -> R for fun => 0} : type_scope.

(* -------------------------------------------------------------------- *)
Section FsFunZmod.
Context {T : choiceType} {R : zmodType}.

Implicit Types f g h : {fsfun T ~> R}.

Definition fs0 : {fsfun T ~> R} := [fsfun].

Definition fsopp f : {fsfun T ~> R} :=
  [fsfun x in finsupp f => -f x].

Definition fsadd f g : {fsfun T ~> R} :=
  [fsfun x in (finsupp f `|` finsupp g)%fset => f x + g x].

Notation "0 %:FS" := fs0 : fsfun_scope.
Notation "- f"    := (fsopp f)  : fsfun_scope.
Notation "f + g"  := (fsadd f g) : fsfun_scope.

Lemma fs0E x : (0%:FS x)%fsfun = 0.
Proof. by rewrite fsfunE. Qed.

Lemma fsoppE f x : (- f)%fsfun x = -(f x).
Proof. by rewrite fsfunE; case: finsuppP => // _; rewrite oppr0. Qed.

Lemma fsaddE f g x : (f + g)%fsfun x = (f x + g x).
Proof.
by rewrite fsfunE in_fsetU; (do 2! case: finsuppP => ? //=); rewrite addr0.
Qed.

Let fsfunwE := (fs0E, fsoppE, fsaddE).

Lemma fsfun_zmod :
  [/\ associative fsadd
    , commutative fsadd
    , left_id fs0 fsadd
    & left_inverse fs0 fsopp fsadd].
Proof. split.
+ by move=> f g h; apply/fsfunP=> x /=; rewrite !fsfunwE addrA.
+ by move=> f g; apply/fsfunP=> x /=; rewrite !fsfunwE addrC.
+ by move=> f; apply/fsfunP=> x /=; rewrite !fsfunwE add0r.
+ by move=> f; apply/fsfunP=> x /=; rewrite !fsfunwE addNr.
Qed.

Let addfA := let: And4 h _ _ _ := fsfun_zmod in h.
Let addfC := let: And4 _ h _ _ := fsfun_zmod in h.
Let add0f := let: And4 _ _ h _ := fsfun_zmod in h.
Let addNf := let: And4 _ _ _ h := fsfun_zmod in h.

Definition fsfun_zmodMixin := ZmodMixin addfA addfC add0f addNf.
Canonical fsfun_zmodType := Eval hnf in ZmodType {fsfun T ~> R} fsfun_zmodMixin.

Lemma supp_fs0 : finsupp 0%R = fset0.
Proof. by rewrite finsupp0. Qed.

Lemma supp_fsN f : finsupp (-f)%fsfun = finsupp f.
Proof.
by apply/fsetP=> x; rewrite !mem_finsupp fsfunwE oppr_eq0.
Qed.

Lemma supp_fsD f g :
  (finsupp (f + g)%R `<=` finsupp f `|` finsupp g)%fset.
Proof.
apply/fsubsetP=> x; rewrite in_fsetU !mem_finsupp !fsfunwE.
case: (f x =P 0) => //= ->; case: (g x =P 0) => //= ->.
by rewrite addr0 eqxx.
Qed.
Lemma mem_fsN x f : (x \in finsupp (-f)%R) -> x \in finsupp f.
Proof. by rewrite supp_fsN. Qed.

Lemma mem_fsD x f g :
  x \in finsupp (f + g)%R -> x \in finsupp f \/ x \in finsupp g.
Proof.
by move/(fsubsetP (supp_fsD _ _)); rewrite in_fsetU (rwP orP).
Qed.
End FsFunZmod.

(* -------------------------------------------------------------------- *)
Section FsFunLmod.
Context {T : choiceType} {R : ringType}.

Implicit Types (c : R) (f g h : {fsfun T ~> R}).

Definition fsscale c f : {fsfun T ~> R} :=
  [fsfun x in finsupp f => c * f x].

Notation "c *: f" := (fsscale c f) : fsfun_scope.

Lemma fsscaleE c f x : (c *: f)%fsfun x = c * f x.
Proof.
by rewrite fsfunE; case: finsuppP => // _; rewrite mulr0.
Qed.

Let fsfunwE := (@fs0E, @fsoppE, @fsaddE, fsscaleE).

Lemma fsfun_lmod :
  [/\ forall c1 c2 f, fsscale c1 (fsscale c2 f) = fsscale (c1 * c2) f
    , left_id 1 fsscale
    , right_distributive fsscale +%R
    & forall f, {morph fsscale^~ f : c1 c2 / c1 + c2}].
Proof. split.
+ by move=> c1 c2 f; apply/fsfunP=> x /=; rewrite !fsfunwE mulrA.
+ by move=> f; apply/fsfunP=> x /=; rewrite !fsfunwE mul1r.
+ by move=> c f g; apply/fsfunP=> x /=; rewrite !fsfunwE mulrDr.
+ by move=> f c1 c2; apply/fsfunP=> x /=; rewrite !fsfunwE mulrDl.
Qed.

Let scale_fsfunA  := let: And4 h _ _ _ := fsfun_lmod in h.
Let scale_fsfun1  := let: And4 _ h _ _ := fsfun_lmod in h.
Let scale_fsfunDr := let: And4 _ _ h _ := fsfun_lmod in h.
Let scale_fsfunDl := let: And4 _ _ _ h := fsfun_lmod in h.

Definition fsfun_lmodMixin :=
  LmodMixin scale_fsfunA scale_fsfun1 scale_fsfunDr scale_fsfunDl.
Canonical fsfun_lmodType :=
  Eval hnf in LmodType R {fsfun T ~> R} fsfun_lmodMixin.
End FsFunLmod.

(* -------------------------------------------------------------------- *)
Section FsFunLmodId.
Context {T : choiceType} {R : idomainType}.

Implicit Types (c : R) (f g h : {fsfun T ~> R}).

Lemma supp_fsZ c f : c != 0 -> finsupp (c *: f)%fsfun = finsupp f.
Proof.
move=> nz_c; apply/fsetP => x; rewrite !mem_finsupp fsscaleE.
by rewrite mulf_eq0 (negbTE nz_c).
Qed.

Lemma mem_fsZ x c f : c != 0 -> x \in finsupp (c *: f)%R -> x \in finsupp f.
Proof. by move/supp_fsZ=> ->. Qed.
End FsFunLmodId.

(* -------------------------------------------------------------------- *)
Definition fsfunwE := (@fs0E, @fsaddE, @fsoppE, @fsscaleE).

(* -------------------------------------------------------------------- *)
Section Combine.
Context {R : ringType} {L : lmodType R}.

Implicit Types (f g h : {fsfun L ~> R}).

Definition combine f : L := \sum_(x : finsupp f) f (fsval x) *: fsval x.

Lemma combinewE E f : (finsupp f `<=` E)%fset ->
  combine f = \sum_(x : E) f (fsval x) *: (fsval x).
Proof.
move=> leEw; pose F x := f x *: x; rewrite /combine.
rewrite -!(big_seq_fsetE _ _ predT F) /= {}/F.
have /permEl h := perm_filterC (mem (finsupp f)) E.
rewrite -{h}(perm_big _ h) big_cat /= 2![X in _+X](big_seq, big1) 1?addr0.
+ move=> x; rewrite mem_filter inE memNfinsupp.
  by case/andP=> [/eqP->]; rewrite scale0r.
apply/perm_big/uniq_perm; rewrite ?(fset_uniq, filter_uniq) //.
by move=> x; rewrite mem_filter inE andb_idr // => /(fsubsetP leEw).
Qed.

Lemma combineE f : combine f = \sum_(x : finsupp f) f (fsval x) *: (fsval x).
Proof. by []. Qed.
End Combine.

(* -------------------------------------------------------------------- *)
Section Weight.
Context {T : choiceType} {R : zmodType}.

Implicit Types (f g h : {fsfun T ~> R}).

Definition weight f := \sum_(x : finsupp f) f (fsval x).

Lemma weightwE E w : (finsupp w `<=` E)%fset ->
  weight w = \sum_(x : E) w (fsval x).
Proof.
move=> leEw; rewrite /weight -!(big_seq_fsetE _ _ predT) /=.
have /permEl h := perm_filterC (mem (finsupp w)) E.
rewrite -{h}(perm_big _ h) big_cat /= 2![X in _+X](big_seq, big1).
+ by move=> x; rewrite mem_filter inE memNfinsupp => /andP[/eqP->].
rewrite addr0; apply/perm_big/uniq_perm; rewrite ?filter_uniq //.
by move=> x; rewrite mem_filter inE andb_idr // => /(fsubsetP leEw).
Qed.

Lemma weightE f : weight f = \sum_(x : finsupp f) f (fsval x).
Proof. by []. Qed.

Lemma weight0 : weight 0 = 0.
Proof. by apply: big1 => -[/= x _ _]; rewrite fsfunwE. Qed.

Lemma weightD f g : weight (f + g) = weight f + weight g.
Proof.
pose E := (finsupp f `|` finsupp g)%fset.
rewrite !(@weightwE E) 1?(fsubsetUl, fsubsetUr, supp_fsD) // {}/E.
by rewrite -big_split /=; apply: eq_bigr=> -[/= x _ _]; rewrite fsaddE.
Qed.
End Weight.

(* -------------------------------------------------------------------- *)
Section Comb.
Context {T : choiceType} {R : numDomainType}.

Implicit Types (w : {fsfun T ~> R}).

Definition conic  w := [forall x : finsupp w, 0 <= w (fsval x)].
Definition convex w := conic w && (weight w == 1).

Lemma conicP w :
  reflect (forall x, x \in finsupp w -> 0 <= w x) (conic w).
Proof. apply: (iffP forallP) => /= [h x|h].
+ by move=> xw; apply: (h (Sub x xw)).
+ by case=> [/= x xw]; apply: h.
Qed.

Lemma convexP w :
  reflect
    [/\ forall x, x \in finsupp w -> 0 <= w x & weight w = 1]
    (convex w).
Proof. by apply: (iffP andP); case=> /conicP h /eqP ->; split. Qed.

Lemma convex_conic w : convex w -> conic w.
Proof. by case/andP. Qed.

Lemma conicwP w : reflect (forall x, 0 <= w x) (conic w).
Proof. apply: (iffP idP).
+ by move/conicP=> h x; case: (finsuppP w x) => // /h.
+ by move=> h; apply/conicP=> x _; apply: h.
Qed.

Lemma conic0 : conic 0.
Proof. by apply/conicP=> x; rewrite fsfunwE. Qed.

Lemma conicD w1 w2 : conic w1 -> conic w2 -> conic (w1 + w2).
Proof.
move=> /conicwP h1 /conicwP h2; apply/conicwP=> x.
by rewrite fsfunwE addr_ge0.
Qed.

Lemma conic_finsuppE x w : conic w -> (x \in finsupp w) = (0 < w x).
Proof.
by move=> /conicwP h; rewrite lt_neqAle h andbT eq_sym; apply: mem_finsupp.
Qed.

Lemma conic_weight_ge0 w : conic w -> 0 <= weight w.
Proof. by move/conicwP=> ge0_w; rewrite weightE; apply: sumr_ge0. Qed.
End Comb.

(* -------------------------------------------------------------------- *)
Section SubConic.
Context {T : choiceType} {R : numDomainType}.

Record conicFun := mkConicFun
  { conic_val :> {fsfun T ~> R}; _ : conic conic_val }.

Canonical conicfun_subType := Eval hnf in [subType for conic_val].
Definition conicfun_eqMixin := [eqMixin of conicFun by <:].
Canonical conicfun_eqType := Eval hnf in EqType conicFun conicfun_eqMixin.
Definition conicfun_choiceMixin := [choiceMixin of conicFun by <:].
Canonical conicfun_choiceType :=
  Eval hnf in ChoiceType conicFun conicfun_choiceMixin.

Definition conicfun_of (_ : phant T) (_ : phant R) := conicFun.
Identity Coercion type_of_conicfun : conicfun_of >-> conicFun.
End SubConic.

Notation "{ 'conic' T ~> R }" :=
  (conicfun_of (Phant T) (Phant R)) : type_scope.

Bind Scope conicfun_scope with conicFun.
Bind Scope conicfun_scope with conicfun_of.

Delimit Scope conicfun_scope with cof.

(* -------------------------------------------------------------------- *)
Section SubConicTheory.
Context {T : choiceType} {R : realDomainType}.

Canonical conicfun_of_subType    := Eval hnf in [subType    of {conic T ~> R}].
Canonical conicfun_of_eqType     := Eval hnf in [eqType     of {conic T ~> R}].
Canonical conicfun_of_choiceType := Eval hnf in [choiceType of {conic T ~> R}].

Implicit Types (w : {conic T ~> R}).

Lemma fconicP w1 w2 : w1 =1 w2 <-> w1 = w2.
Proof. by rewrite fsfunP (rwP val_eqP) (rwP eqP). Qed.

Lemma gt0_fconic w x : x \in finsupp w -> 0 < w x.
Proof. by rewrite conic_finsuppE // (valP w). Qed.

Lemma ge0_fconic w x : 0 <= w x.
Proof. by move/conicwP: (valP w); apply. Qed.

(* We have to lock the definitions *)
Definition conicf0 : {conic T ~> R} :=
  nosimpl (mkConicFun conic0).

Definition conicfD : _ -> _ -> {conic T ~> R} :=
  nosimpl (fun w1 w2 => mkConicFun (conicD (valP w1) (valP w2))).

Notation "0 %:PFS" := conicf0 : conicfun_scope.
Notation "f + g" := (conicfD f g) : conicfun_scope.

Lemma fconic0E x : (0%:PFS)%cof x = 0.
Proof. by rewrite fsfunwE. Qed.

Lemma fconicDE w1 w2 x : (w1 + w2)%cof x = w1 x + w2 x.
Proof. by rewrite fsfunwE. Qed.

Definition fconicwE := (fconic0E, fconicDE).

Lemma conic_comoid_r :
  [/\ associative conicfD
    , left_id conicf0 conicfD
    , right_id conicf0 conicfD
    & commutative conicfD].
Proof. split.
+ by move=> w1 w2 w3; apply/fconicP => x; rewrite !fconicwE addrA.
+ by move=> w; apply/fconicP => x; rewrite !fconicwE add0r.
+ by move=> w; apply/fconicP => x; rewrite !fconicwE addr0.
+ by move=> w1 w2; apply/fconicP => x; rewrite !fconicwE addrC.
Qed.

Let addpA := let: And4 h _ _ _ := conic_comoid_r in h.
Let add0p := let: And4 _ h _ _ := conic_comoid_r in h.
Let addp0 := let: And4 _ _ h _ := conic_comoid_r in h.
Let addpC := let: And4 _ _ _ h := conic_comoid_r in h.

Canonical conic_monoid := Monoid.Law addpA add0p addp0.
Canonical conic_comoid := Monoid.ComLaw addpC.

Lemma mem_coffinsupp w x : (x \in finsupp w) = (0 < w x).
Proof. by rewrite mem_finsupp lt_neqAle eq_sym ge0_fconic andbT. Qed.

Lemma coffinsupp0 : finsupp (0%:PFS)%cof = fset0.
Proof. by rewrite supp_fs0. Qed.

Lemma coffinsuppD w1 w2 :
  finsupp (w1 + w2)%cof = (finsupp w1 `|` finsupp w2)%fset.
Proof.
apply/fsetP=> x; rewrite in_fsetE !mem_coffinsupp fconicwE.
have := ge0_fconic w1 x; rewrite le_eqVlt => /orP[].
+ by move/eqP=> <-; rewrite ltxx add0r.
+ by move=> gt0_w1; rewrite gt0_w1 ltr_paddr // ge0_fconic.
Qed.

Lemma ge0_cofweight w : 0 <= weight w.
Proof. by apply/conic_weight_ge0/valP. Qed.
End SubConicTheory.

Notation "0 %:PFS" := conicf0 : conicfun_scope.
Notation "f + g" := (conicfD f g) : conicfun_scope.

(* -------------------------------------------------------------------- *)
Section ConicUniform.
Context {T : choiceType} {R : numDomainType}.

Implicit Type S : {fset T}.

Lemma fconicu_r S : @conic T R [fsfun _ in S => 1].
Proof.
apply/conicP=> x /(fsubsetP (finsupp_sub _ _ _)) x_in.
by rewrite fsfunE ifT.
Qed.

Definition fconicu : {fset T} -> {conic T ~> R} :=
  nosimpl (fun S => mkConicFun (fconicu_r S)).

Lemma fconicuE S x : fconicu S x = (x \in S)%:R.
Proof. by rewrite fsfunE; case: ifP. Qed.

Lemma finsupp_fconicu S : finsupp (fconicu S) = S.
Proof.
apply/fsetP => y; rewrite mem_finsupp fconicuE.
by rewrite pnatr_eq0 eqb0 negbK.
Qed.
End ConicUniform.

(* -------------------------------------------------------------------- *)
Section SubConvex.
Context {T : choiceType} {R : numDomainType}.

Record convexFun := mkConvexfun
  { convex_val :> {fsfun T ~> R}; _ : convex convex_val }.

Canonical convexfun_subType := Eval hnf in [subType for convex_val].
Definition convexfun_eqMixin := [eqMixin of convexFun by <:].
Canonical convexfun_eqType := Eval hnf in EqType convexFun convexfun_eqMixin.
Definition convexfun_choiceMixin := [choiceMixin of convexFun by <:].
Canonical convexfun_choiceType :=
  Eval hnf in ChoiceType convexFun convexfun_choiceMixin.

Definition convexfun_of (_ : phant T) (_ : phant R) := convexFun.
Identity Coercion type_of_convexfun : convexfun_of >-> convexFun.
End SubConvex.

Notation "{ 'convex' T ~> R }" :=
  (convexfun_of (Phant T) (Phant R)) : type_scope.

Bind Scope convexfun_scope with convexFun.
Bind Scope convexfun_scope with convexfun_of.

Delimit Scope convexfun_scope with cvf.

(* -------------------------------------------------------------------- *)
Section SubConvexTheory.
Context {T : choiceType} {R : realDomainType}.

Canonical convexfun_of_subType    := Eval hnf in [subType    of {convex T ~> R}].
Canonical convexfun_of_eqType     := Eval hnf in [eqType     of {convex T ~> R}].
Canonical convexfun_of_choiceType := Eval hnf in [choiceType of {convex T ~> R}].

Implicit Types (w : {convex T ~> R}).

Lemma fconvexP w1 w2 : w1 =1 w2 <-> w1 = w2.
Proof. by rewrite fsfunP (rwP val_eqP) (rwP eqP). Qed.

Lemma conic_fconvex w : conic w.
Proof. by apply/convex_conic/valP. Qed.

Lemma convex_fconvex w : convex w.
Proof. by apply/valP. Qed.

Lemma gt0_fconvex w x : x \in finsupp w -> 0 < w x.
Proof. by rewrite conic_finsuppE //; apply/conic_fconvex. Qed.

Lemma ge0_fconvex w x : 0 <= w x.
Proof. by move/conicwP: (conic_fconvex w); apply. Qed.

Lemma ge0_cvweight w : 0 <= weight w.
Proof. by apply/conic_weight_ge0/conic_fconvex. Qed.

Lemma wgt1_fconvex w : weight w = 1.
Proof. by case/convexP: (valP w). Qed.

Lemma le1_fconvex w x : w x <= 1.
Proof.
case: finsuppP => // xw; rewrite -(wgt1_fconvex w) weightE.
rewrite -(big_seq_fsetE _ _ predT) /= -(fsetD1K xw).
rewrite big_fsetU1 ?fsetD11 //= ler_addl.
by apply: sumr_ge0=> i _; apply: ge0_fconvex.
Qed.

Lemma fconvex_insupp_neq0 w : (finsupp w == fset0) = false.
Proof.
apply/negP=> /eqP zw; have := wgt1_fconvex w.
by rewrite weightE zw big_fset0 (rwP eqP) eq_sym oner_eq0.
Qed.
End SubConvexTheory.

(* -------------------------------------------------------------------- *)
Section CvxDirac.
Context {T : choiceType} {R : realDomainType}.

Lemma fcvx1_r x : @convex T R [fsfun _ in [fset x]%fset => 1].
Proof. apply/convexP; split=> /=.
+ by move=> y _; rewrite fsfunE; case: ifP.
+ rewrite (weightwE (E := [fset x]%fset)); last first.
    by rewrite big_fset1 /= fsfunE fset11.
  apply/fsubsetP=> y; rewrite mem_finsupp fsfunE in_fset1.
  by case: ifP => //; rewrite eqxx.
Qed.

Definition fcvx1 : T -> {convex T ~> R} :=
  nosimpl (fun x => mkConvexfun (fcvx1_r x)).

Lemma fcvx1E x y : fcvx1 x y = (y == x)%:R.
Proof. by rewrite fsfunE in_fset1; case: ifP. Qed.

Lemma finsupp_fcvx1 x : finsupp (fcvx1 x) = [fset x]%fset.
Proof.
apply/fsetP=> y; rewrite in_fset1 mem_finsupp fcvx1E.
by rewrite pnatr_eq0 eqb0 negbK.
Qed.

Lemma mem_fcvx1 x y : (y \in finsupp (fcvx1 x)) = (y == x).
Proof. by rewrite finsupp_fcvx1 in_fset1. Qed.

Lemma fcvx1E_finsupp (w : {convex T ~> R}) x y :
  (finsupp w `<=` [fset x])%fset -> w y = (y == x)%:R.
Proof.
rewrite fsubset1 fconvex_insupp_neq0 orbF => /eqP fw.
case: finsuppP; rewrite fw in_fset1; first by move=> /negbTE->.
move=> /eqP ->; move: (wgt1_fconvex w); rewrite weightE eqxx /=.
by rewrite fw big_fset1 /=.
Qed.
End CvxDirac.

(*-------------------------------------------------------------------- *)
Section CvxDiracCombine.
Context {R : realDomainType} {L : lmodType R}.

Lemma combine_fcvx1 (x : L) : combine (fcvx1 x) = x.
Proof.
by rewrite combineE finsupp_fcvx1 big_fset1 fcvx1E eqxx scale1r.
Qed.
End CvxDiracCombine.

(* -------------------------------------------------------------------- *)
Section CvxSegment.
Context {R : realDomainType} {L : lmodType R}.

Definition clamp a : R :=
  if 0 <= a <= 1 then a else 0.

Lemma clamp_id a : 0 <= a <= 1 -> clamp a = a.
Proof. by rewrite /clamp => ->. Qed.

Lemma rg01_clamp a : 0 <= clamp a <= 1.
Proof.
by rewrite /clamp; case: ifP => // _; rewrite lexx ler01.
Qed.

Lemma ge0_clamp a : 0 <= clamp a.
Proof. by case/andP: (rg01_clamp a). Qed.

Lemma le1_clamp a : clamp a <= 1.
Proof. by case/andP: (rg01_clamp a). Qed.

Lemma ge0_1Bclamp a : 0 <= 1 - clamp a.
Proof. by rewrite subr_ge0 le1_clamp. Qed.

Lemma le1_1Bclamp a : 1 - clamp a <= 1.
Proof. by rewrite ler_subl_addr ler_addl ge0_clamp. Qed.

Lemma fseg_r a x y :
  @convex L R [fsfun z in [fset x; y]%fset =>
     (z == x)%:R * (1 - clamp a) + (z == y)%:R * clamp a].
Proof. apply/convexP; split=> /=.
+ move=> z _; rewrite fsfunE; case: ifP => // _.
  by rewrite addr_ge0 // mulr_ge0 // (ler0n, ge0_clamp, ge0_1Bclamp).
+ rewrite (@weightwE _ _ [fset x; y]%fset) ?finsupp_sub //.
  case: (x =P y) => [->|/eqP ne_xy]; first rewrite fsetUid big_fset1.
  - by rewrite fsfunE /= fset11 eqxx !mul1r addrNK.
  rewrite -(big_seq_fsetE _ _ predT) /= big_fsetU1 ?in_fset1 //=.
  rewrite big_seq_fset1 !fsfunE !(fset21, fset22) [y == x]eq_sym.
  by rewrite !(eqxx, negbTE ne_xy) !Monoid.simpm /= addrNK.
Qed.

Definition fseg : _ -> _ -> _ -> {convex L ~> R} :=
  nosimpl (fun a x y => mkConvexfun (fseg_r a x y)).

Lemma fsegE a x y z :
  fseg a x y z = (z == x)%:R * (1 - clamp a) + (z == y)%:R * clamp a.
Proof.
rewrite fsfunE in_fset2; do! case: (z =P _) => //= _.
by rewrite !mul0r addr0.
Qed.

Lemma finsupp_fseg a x y : (finsupp (fseg a x y) `<=` [fset x; y])%fset.
Proof. by apply: finsupp_sub. Qed.

Lemma combine_fseg a x y :
  combine (fseg a x y) = (1 - clamp a) *: x + clamp a *: y.
Proof.
rewrite (combinewE (finsupp_fseg a x y)); case: (x =P y) => [<-|].
+ by rewrite fsetUid big_fset1 fsegE /= eqxx !mul1r -scalerDl.
move/eqP => ne_xy; pose F z := fseg a x y z *: z.
rewrite -(big_seq_fsetE _ _ predT F) {}/F /=.
rewrite big_fsetU1 ?in_fset1 //= big_seq_fset1 !fsegE.
by rewrite [y == x]eq_sym !(eqxx, negbTE ne_xy) !Monoid.simpm.
Qed.

Lemma cvxsegP x p q :
      (exists2 a, 0 <= a <= 1 & x = (1 - a) *: p + a *: q)
  <-> (exists2 w : {convex L ~> R},
         (finsupp w `<=` [fset p; q])%fset & x = combine w).
Proof. split.
+ case=> a rg01_a ->; exists (fseg a p q).
  - by apply: finsupp_fseg.
  - by rewrite combine_fseg clamp_id.
+ case=> w le_w_pq ->; rewrite (combinewE le_w_pq); exists (w q).
  - by rewrite ge0_fconvex le1_fconvex.
  case: (p =P q) le_w_pq => [<-|/eqP nz_pq] le_w_pq.
  - rewrite fsetUid big_fset1 /= -scalerDl subrK scale1r.
    suff ->: w p = 1 by rewrite scale1r.
    move: le_w_pq; rewrite fsetUid => /fcvx1E_finsupp.
    by move=> ->; rewrite eqxx.
  pose F x := w x *: x; rewrite -(big_seq_fsetE _ _ predT F) /=.
  rewrite big_fsetU1 ?in_fset1 //= big_seq_fset1 {}/F.
  move: (weightwE le_w_pq); rewrite -(big_seq_fsetE _ _ predT) /=.
  rewrite big_fsetU1 ?in_fset1 // big_seq_fset1 /=.
  by rewrite wgt1_fconvex => ->; rewrite addrK.
Qed.
End CvxSegment.

(* -------------------------------------------------------------------- *)
Section Bary.
Context {R : realDomainType} {L : lmodType R}.

Implicit Types (V : {fset L}) (w : {convex L ~> R}).

Definition bary (V : {fset L}) :=
  fun x : L => exists2 w : {convex L ~> R},
    {subset finsupp w <= V} & x = combine w.

Notation "x \bary V" := (bary V x) : form_scope.

Lemma bary_subset V1 V2 x :
  {subset V1 <= V2} -> x \bary V1 -> x \bary V2.
Proof.
move=> le_V1_V2 [w le_w_V1 ->]; exists w => //.
by move=> {}x /le_w_V1 /le_V1_V2.
Qed.

Lemma bary1 x : x \bary [fset x]%fset.
Proof.
exists (fcvx1 x); last by rewrite combine_fcvx1.
by move=> y; rewrite mem_fcvx1 => /eqP->; rewrite fset11.
Qed.
End Bary.

(* -------------------------------------------------------------------- *)
Section ConvexPred.
Context {R : realFieldType} {L : lmodType R} (P : pred L).

Definition convex_pred :=
  forall x y : L, x \in P -> y \in P ->
    forall a : R, 0 <= a <= 1 -> (1-a) *: x + a *: y \in P.

Lemma combine2C (x y : L) (α : R) :
  (1-α) *: x + α *: y = (1 - (1 - α)) *: y + (1 - α) *: x.
Proof.
by rewrite subKr addrC.
Qed.

Lemma combine2_line (v w : L) α :
  (1 - α) *: v + α *: w = v + α *: (w - v).
Proof.
by rewrite scalerBl scale1r addrAC -addrA -scalerBr.
Qed.

Hypothesis cvxP : convex_pred.

(* FIXME: TO BE REWORKED *)
Lemma convexW (w : {convex L ~> R}) :
  {in finsupp w, forall x, x \in P} -> combine w \in P.
Proof.
move=> wP; rewrite combineE; pose F x := w x *: x.
rewrite -!(big_seq_fsetE _ _ predT F) /= {}/F.
move: {-2}(finsupp _) (erefl (finsupp w)) => X.
elim/finSet_rect: X w wP => X ih w wP XE.
have /negP/negP := fconvex_insupp_neq0 w.
rewrite -XE => /fset0Pn[x xX]; rewrite -(fsetD1K xX).
rewrite big_fsetU1 ?fsetD11 //=.
have w1: \sum_(y <- (X `\ x)%fset) w y = 1 - w x.
+ rewrite -(wgt1_fconvex w) weightE -(big_seq_fsetE _ _ predT) /=.
  rewrite -XE -[in RHS](fsetD1K xX) big_fsetU1 ?fsetD11 //=.
  by rewrite addrAC subrr add0r.
have := le1_fconvex w x; rewrite le_eqVlt => /orP[/eqP wxE|lt1_wx].
+ rewrite wxE scale1r big1_seq /= ?addr0; last by apply: wP; rewrite -XE.
  move=> y yXDx; rewrite (rwP eqP); suff ->: w y = 0 by rewrite scale0r.
  move/eqP: w1; rewrite wxE subrr psumr_eq0 => [z _|].
  - by apply: ge0_fconvex.
  - by move/allP=> h; apply/eqP/h.
pose wR : {fsfun _ ~> _} := [fsfun a in (X `\ x)%fset => w a / (1 - w x)].
have hE: \sum_(y <- (X `\ x)%fset) w y *: y
        = (1 - w x) *: \sum_(y <- (X `\ x)%fset) wR y *: y.
+ rewrite scaler_sumr !big_seq; apply: eq_bigr=> y yXDx.
  rewrite scalerA fsfunE yXDx mulrCA divff ?mulr1 //.
  by rewrite subr_eq0 eq_sym lt_eqF.
rewrite hE addrC; (apply: cvxP; try by apply: wP; rewrite -XE); last first.
+ by rewrite ge0_fconvex le1_fconvex.
have cvx_wR: convex wR; first (apply/convexP; split).
+ move=> y _; rewrite fsfunE; case: ifP=> // _.
  by rewrite divr_ge0 1?ge0_fconvex // subr_ge0 le1_fconvex.
+ rewrite (weightwE (E := (X `\ x)%fset)).
  - by apply: finsupp_sub.
  - rewrite (eq_bigr (fun y => w (val y) / (1 - w x))) /=.
    * by move=> y _; rewrite fsfunE fsvalP.
    rewrite -mulr_suml -(big_seq_fsetE _ _ predT w) /=.
    by rewrite w1 divff // subr_eq0 eq_sym lt_eqF.
have supp_wR: (finsupp wR = X `\ x)%fset.
+ apply/fsetP=> y; rewrite mem_finsupp fsfunE.
  case: ifP; rewrite ?eqxx //= => yXdx.
  rewrite mulf_eq0 invr_eq0 gt_eqF ?gt0_fconvex //=.
  * by rewrite -XE; apply/fsubsetP/fsubD1set: yXdx.
  by rewrite subr_eq0 eq_sym lt_eqF.
have /= := ih (X `\ x)%fset _ (mkConvexfun cvx_wR); apply=> //.
+ by apply: fproperD1.
+ by move=> y; rewrite supp_wR in_fsetD1 => /andP[_]; rewrite XE => /wP.
Qed.
End ConvexPred.

(* -------------------------------------------------------------------- *)
Section VectToFsFun.
Context {T : choiceType} {R : ringType}.

Definition frank (S : {fset T}) (v : S) : 'I_#|`S| :=
  cast_ord (esym (cardfE _)) (enum_rank v).

Lemma frankK (S : {fset T}) :
  cancel (fun i : 'I_#|`S| => [`fnthP i]%fset) (@frank S).
Proof.
move=> i; apply/(@cast_ord_inj _ _ (cardfE S))/eqP.
rewrite cast_ordKV -(inj_eq (enum_val_inj)) enum_rankK -(rwP eqP).
apply/val_eqP => /=; set j := cast_ord _ i.
rewrite /fnth (tnth_nth (val (enum_default j))) /= {1}enum_fsetE.
by rewrite (nth_map (enum_default j)) // -cardE -cardfE.
Qed.

Lemma fnthK (S : {fset T}) :
  cancel (@frank S) (fun i : 'I_#|`S| => [`fnthP i]%fset).
Proof.
move=> x; apply/val_eqP/eqP => /=; rewrite /fnth.
rewrite (tnth_nth (val x)) /= enum_fsetE /=.
by rewrite (nth_map x)? nth_enum_rank // -cardE.
Qed.

Lemma val_fnthK (S : {fset T}) (v : S) : fnth (frank v) = fsval v.
Proof. by have := fnthK v => /(congr1 val). Qed.

Lemma bij_frank (S : {fset T}) : bijective (@frank S).
Proof. exact: (Bijective (@fnthK _) (@frankK S)). Qed.

Definition vect_to_fsfun (I : {fset T}) (c : 'cV[R]_#|`I|) : {fsfun T ~> R} :=
  [fsfun v : I => c (frank v) 0].

Lemma finsupp_vect_to_fsfun (I : {fset T}) (c : 'cV[R]_#|`I|) :
  (finsupp (@vect_to_fsfun I c) `<=` I)%fset.
Proof.
apply/fsubsetP=> x; rewrite mem_finsupp fsfun_ffun.
by case: insubP => //=; rewrite eqxx.
Qed.
End VectToFsFun.


(* -------------------------------------------------------------------- *)
Section VectToFsFunTheory.
Context {T : choiceType} {R : realFieldType}.

Lemma conic_vect_to_fsfun (I : {fset T}) (c : 'cV[R]_#|`I|) :
  (0) <=m (c) -> conic (vect_to_fsfun c).
Proof.
move=> ge0_c; apply/conicwP => x; rewrite fsfun_ffun.
by case: insubP => //= i _ _; apply: gev0P.
Qed.

Lemma convex_vect_to_fsfun (I : {fset T}) (c : 'cV[R]_#|`I|) :
  (0) <=m (c) -> '[const_mx 1, c] = 1 -> convex (vect_to_fsfun c).
Proof.
move=> ge0_c Σc_eq_1; rewrite /convex conic_vect_to_fsfun //=.
rewrite (weightwE (finsupp_vect_to_fsfun _)) -(rwP eqP).
move: Σc_eq_1; rewrite vdotC vdotr_const_mx1 => <-.
rewrite (reindex (@frank _ _)) /=; first by apply/onW_bij/bij_frank.
apply: eq_bigr=> i _; rewrite fsfun_ffun insubT //=.
by move=> hin; rewrite fsetsubE.
Qed.
End VectToFsFunTheory.
