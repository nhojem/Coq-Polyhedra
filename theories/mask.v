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

Definition fmask_nth_ (mas : cmask) (k : 'I_n) :=
  nth m (mask mas (iota 0 m)) k.

Program Definition fmask_nth (mas : cmask) (k : 'I_n) :=
  @Ordinal m (fmask_nth_ mas k) _.

Next Obligation.
suff: fmask_nth_ mas k \in iota 0 m
  by rewrite mem_iota add0n => /andP [].
apply/(mem_subseq (mask_subseq mas _))/mem_nth.
rewrite size_mask ?card_fmask ?ltn_ord //.
by rewrite size_iota size_tuple.
Qed.

Lemma fmask_nth_mono (mas : cmask) :
  {mono (fmask_nth mas) : x y/ (x < y)%nat}.
Proof.
Admitted.

End ChooseMask.

Notation "m '.-choose' n" := (cmask m n) (at level 0, format "m .-choose  n").
