From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation "##| p |" := (count id p) (at level 0, p at level 99, format "##| p |").

Section Mask.

Definition maskI m m' := map (fun x => x.1 && x.2) (zip m m').

End Mask.

Section ChooseMask.

Context (m n : nat).
Record cmask :=
  CMask { smask :> m.-tuple bool;
          _ : ##|smask| == n }.

Canonical cmask_subType := Eval hnf in [subType for smask].
Definition cmask_eqMixin := [eqMixin of cmask by <:].
Canonical cmask_eqType := EqType _ cmask_eqMixin.
Definition cmask_choiceMixin := [choiceMixin of cmask by <:].
Canonical cmask_choiceType := ChoiceType _ cmask_choiceMixin.
Definition cmask_countMixin := [countMixin of cmask by <:].
Canonical cmask_countType := CountType _ cmask_countMixin.
Canonical cmask_subCountType := [subCountType of cmask].
Definition cmask_finMixin := [finMixin of cmask by <:].
Canonical cmask_finType := FinType _ cmask_finMixin.

Lemma card_fmask (mas : cmask) : ##|mas| = n.
Proof. by case: mas => ? /= /eqP. Qed.

Lemma size_fmask (mas : cmask) : size mas = m.
Proof. by rewrite size_tuple. Qed.

Definition index_list (mas : cmask) : seq 'I_m := (mask mas (enum 'I_m)).

Lemma index_listP (mas : cmask) (k : 'I_m) :
  (nth false mas k = true) <-> k \in index_list mas.
Proof.
have k_mem: (k \in enum 'I_m) by
  rewrite -(@nth_ord_enum _ k k) mem_nth ?size_enum_ord ?ltn_ord.
rewrite /index_list mask_filter ?mask_enum_ord /=.
- by rewrite mem_filter k_mem andbT mem_filter k_mem andbT.
- by move: (iota_uniq 0 m); rewrite -val_enum_ord=> /map_uniq.
Qed.

Lemma size_index_list (mas : cmask) : size (index_list mas) = n.
Proof. by rewrite size_mask ?card_fmask ?size_enum_ord ?size_fmask. Qed.

Definition fmask_nth_ (mas : cmask) (k : 'I_n) :=
  nth m [seq val i | i <- index_list mas] k.

Program Definition fmask_nth (mas : cmask) (k : 'I_n) :=
  @Ordinal m (fmask_nth_ mas k) _.
Next Obligation.
rewrite /fmask_nth_.
move: (@mem_nth _ m [seq val i | i <- index_list mas] k).
set e := nth _ _ _.
rewrite size_map size_index_list ltn_ord /=.
by case/(_ isT)/mapP=> x + ->; rewrite ltn_ord.
Qed.

Lemma fmask_nth_mono (mas : cmask) :
  {mono (fmask_nth mas) : x y/ (x < y)%nat}.
Proof.
Admitted.

Lemma card_maskF (s : seq bool): ##|s| = 0 -> s = nseq (size s) false.
Proof.
elim : s => //= a l IH.
move/eqP; rewrite addn_eq0=> /andP []; rewrite eqb0 => /negbTE ->.
by move/eqP/IH=> <-.
Qed.

(*TODO : move somewhere else*)
Lemma map_filter {T1 T2 : Type} (s : seq T1) (f g : T1 -> T2) (P Q : pred T1) :
  f =1 g -> P =1 Q -> [seq f x | x <- s & P x] = [seq g x | x <- s & Q x].
Proof.
move=> fg PQ.
elim: s=> //= a l.
case/boolP: (P a).
- by rewrite PQ => -> /= ->; rewrite fg.
- by rewrite PQ => /negbTE ->.
Qed.

Lemma index_list_mask {T : Type} (s : m.-tuple T) (x : T) (mas : cmask):
  mask mas s = [seq nth x s (val i) | i <- enum 'I_m & i \in index_list mas].
Proof.
case: s=> /= s; case: mas => -[] mas /=.
rewrite /index_list /=.
elim: m mas s n.
- move=> mas s q /eqP /size0nil -> _ _ ; rewrite !mask0s.
  by symmetry; apply/size0nil; rewrite size_map filter_pred0.
- move=> p IH; case=> // hb tb [] //= hs ts q.
  rewrite enum_ordS /=.
  case: hb => /=.
  + rewrite add1n => /eqP/eq_add_S size_tb /eqP card_tb /eqP/eq_add_S size_ts.
    rewrite (IH _ _ q.-1) ?size_tb ?size_ts -?card_tb -?pred_Sn //.
    congr cons. rewrite filter_map -map_comp /=.
    apply/map_filter=> i //=; rewrite in_cons lift_eqF /= -map_mask mem_map //.
    exact: lift_inj.
  + rewrite add0n=> /eqP/eq_add_S size_tb /eqP card_tb /eqP/eq_add_S size_ts.
    have ->: ord0 \in mask tb [seq lift ord0 i | i <- enum 'I_p] = false.
    - rewrite -map_mask; apply/negbTE/negP.
      by case/mapP=> ? _ /eqP; rewrite eq_liftF.
    rewrite (IH _ _ q) ?size_tb ?size_ts ?card_tb //.
    rewrite filter_map -map_comp /=; apply/map_filter=> i //=.
    rewrite -map_mask mem_map //.
    exact: lift_inj.
Qed.


Lemma fmask_nthP_ {T : Type} (s : m.-tuple T) (x : T) (k : 'I_n) (mas : cmask) (k' : 'I_m):
  nth x (mask mas s) k = nth x s (fmask_nth mas k).
Proof.
rewrite (index_list_mask s x) (nth_map k') /=.
- rewrite /fmask_nth /= /fmask_nth_ /index_list mask_enum_ord /=.
  congr nth; rewrite (nth_map k').
  congr val; congr nth; apply/eq_filter=> /= y.
  by rewrite mem_filter mem_enum inE andbT.
- by rewrite -mask_enum_ord size_mask ?size_fmask ?size_enum_ord ?card_fmask.
- rewrite /index_list -mask_filter ?enum_uniq //.
  by rewrite size_mask ?card_fmask ?size_fmask ?size_enum_ord.
Qed.

Lemma fmask_nthP {T : Type} (s : m.-tuple T) (x : T) (k : 'I_n) (mas : cmask) :
  nth x (mask mas s) k = nth x s (fmask_nth mas k).
Proof.
move: (fmask_nthP_ s x k mas).
rewrite /fmask_nth /= /fmask_nth_ /index_list.
case: mas=> /= -[] /=; case: s=> /=.
case: m.
- by move=> s /eqP/size0nil -> ?; rewrite mask0 !nth_nil.
- by move=> ?????? /(_ ord0).
Qed.


End ChooseMask.

Notation "m '.-choose' n" := (cmask m n) (at level 0, format "m .-choose  n").
