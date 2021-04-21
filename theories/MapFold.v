(* -------------------------------------------------------------------- *)
(* ------- *) Require Import FMaps FMapAVL.
From mathcomp Require Import all_ssreflect.

Open Scope order_scope.

Import Order.Theory.

(* -------------------------------------------------------------------- *)
Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

(* -------------------------------------------------------------------- *)
Module Type Sig.
Parameters (d : unit) (T : orderType d).
End Sig.

Module OType (O: Sig) <: OrderedType.
Definition t : Type := O.T.

Definition eq (x y : t) : Prop := x = y.
Definition lt (x y : t) : Prop := x < y.

Lemma eq_refl (x : t) : eq x x.
Proof. done. Qed.

Lemma eq_sym (x y : t) : eq x y -> eq y x.
Proof. done. Qed.

Lemma eq_trans (x y z : t) : eq x y -> eq y z -> eq x z.
Proof. by move=> eqxy eqyz; transitivity y. Qed.

Lemma lt_trans (x y z : t) : lt x y -> lt y z -> lt x z.
Proof. by apply: lt_trans. Qed.

Lemma lt_not_eq (x y : t) : lt x y -> ~ (eq x y).
Proof. by move/lt_eqF/negbT/eqP. Qed.

Definition compare (x y : t) :=
  match ltgtP x y with
  | RelOrder.ComparelEq eq => EQ (lt := lt) eq
  | RelOrder.ComparelLt lt => LT lt
  | RelOrder.ComparelGt gt => GT gt
  end.

Lemma eq_dec (x y : t) : {eq x y}+{~ eq x y}.
Proof. by case: (x =P y)=> ?; [left | right]. Qed.
End OType.

(* -------------------------------------------------------------------- *)
Module M (O : Sig).
  Module OT := OType O.
  Include FMapAVL.Make(OT).
  Include O.

  Definition IsBindings {U} (m : t U) (bds : seq.seq (T * U)) :=
    [/\ perm_eq (unzip1 bds) (unzip1 (elements m))
      & forall k, find k m = ohead [seq kv.2 | kv <- bds & kv.1 == k]].
End M.

Module F (O : Sig).
  Module MO := M O.
  Include FMapFacts.Facts(MO).
  Include FMapFacts.Properties(MO).

  Lemma uniq_keys {U} (m : MO.t U) : uniq (unzip1 (MO.elements m)).
  Proof.
  elim: (MO.elements_3w m) => // -[k v] bds /= + _ ->.
  rewrite andbT => h; apply/negP; apply/contra_not: h.
  elim: bds => // -[k2 v2] bds ih /=; rewrite in_cons.
  case/orP=> [/eqP->|{}/ih ih]; first by apply: InA_cons_hd.
  by apply: InA_cons_tl.
  Qed.

  Lemma inkeysP {U} (m : MO.t U) k :
    reflect (MO.In k m) (k \in unzip1 (MO.elements m)).
  Proof. apply: (iffP idP).
  - rewrite elements_in_iff; elim: (MO.elements m) => //.
    case=> k' v bds ih /=; rewrite in_cons; case/orP.
    - by move=> /eqP<-; exists v; apply: InA_cons_hd.
    - by case/ih=> v' {}ih; exists v'; apply: InA_cons_tl.
  - rewrite elements_in_iff => -[v]; elim.
    - by case=> [k' v'] bds /= [/= <- _]; rewrite mem_head.
    - by case=> [k' v'] bds _ ih; rewrite mem_behead.
  Qed.

  Lemma elements_Mequal {U} (m1 m2 : MO.t U) :
    MO.Equal m1 m2 -> perm_eq (unzip1 (MO.elements m1)) (unzip1 (MO.elements m2)).
  Proof.
  have wlog: forall (m1 m2 : MO.t U), MO.Equal m1 m2 ->
    {subset unzip1 (MO.elements m1) <= unzip1 (MO.elements m2)}.
  - move=> {m1 m2} m1 m2 + k; move/In_m => /(_ _ _ (erefl k)).
    by case=> le _ /inkeysP ?; apply/inkeysP/le.
  move=> eqm; apply: uniq_perm; try exact: uniq_keys.
  by move=> k; apply/idP/idP; apply: wlog.
  Qed.

  Lemma IsBindings0 {U} (m : MO.t U) : MO.IsBindings m [::] -> MO.Empty m.
  Proof.
  case=> /=; rewrite perm_sym => /perm_nilP + _.
  move/(congr1 size); rewrite size_map /=.
  by case E: (MO.elements _) => // _; apply/elements_Empty.
  Qed.

  Lemma IsBindingsS {U} (m : MO.t U) bd bds :
    MO.IsBindings m (bd :: bds) ->
      exists sm, [/\
          ~(MO.In bd.1 sm)
        , MO.Equal m (MO.add bd.1 bd.2 sm)
        & MO.IsBindings sm bds
      ].
  Proof.
  case=> eqbds hbds; exists (MO.remove bd.1 m).
  have /= /andP[mem_bds uq_bds]: uniq (bd.1 :: unzip1 bds).
  - by rewrite (perm_uniq eqbds) uniq_keys.
  do! split; first by apply: MO.remove_1.
  - move=> k; case: (bd.1 =P k) => [<-|/[dup] /eqP ne neP].
    - by rewrite hbds /= eqxx /= add_eq_o.
    - by rewrite add_neq_o // remove_neq_o.
  - apply: uniq_perm=> //; first by apply: uniq_keys.
    move=> k; apply/idP/inkeysP.
    - move=> k_bds; suff mem_km: MO.In k m.
      - rewrite remove_neq_in_iff //; apply/eqP.
        by apply/contraNneq: mem_bds=> ->.
      apply/inkeysP; rewrite -(perm_mem eqbds) /=.
      by rewrite in_cons k_bds orbT.
    - rewrite remove_in_iff => -[/eqP ne /inkeysP].
      by rewrite -(perm_mem eqbds) /= in_cons eq_sym (negbTE ne).
  - move=> k; case: (bd.1 =P k) => [<-|/[dup] neq /eqP neqP].
    - rewrite remove_eq_o //;
        elim: {uq_bds eqbds hbds} bds mem_bds => //= k' v' ih.
      rewrite in_cons negb_or => /andP[ne {}/ih ih].
      by rewrite [_ == bd.1]eq_sym (negbTE ne) -ih.
    - by rewrite remove_neq_o // hbds /= (negbTE neqP).
  Qed.
End F.

Module MapFold (O : Sig).

Module FO := F O.
Import FO.MO.
Notation fmap := t.

(* -------------------------------------------------------------------- *)
Require Import Classes.RelationClasses.

Definition fP_d {U A} (f : T -> U -> A -> A) rA :=
  `{Proper (eq ==> eq ==> rA ==> rA) f}.

Definition fC_d {U A} (f : T -> U -> A -> A) (rA : A -> A -> Prop)  :=
  forall k1 v1 k2 v2 a, rA (f k1 v1 (f k2 v2 a)) (f k2 v2 (f k1 v1 a)).

Definition fcomp_d {U A} (f : T -> U -> A -> A) (rA : A -> A -> Prop) :=
  forall k v a1 a2, rA a1 a2 -> rA (f k v a1) (f k v a2).

Lemma L {U A} (f : T -> U -> A -> A) (rA : A -> A -> Prop) m x0 bds :
  `{Equivalence rA} ->
  fP_d f rA -> fC_d f rA -> fcomp_d f rA ->
  IsBindings m bds ->
  rA (fold f m x0) (foldr (fun kv a => f kv.1 kv.2 a) x0 bds).
Proof.
move=> rAE fP fC fcomp.
elim: bds m => [|bd bds ih] m.
- move/FO.IsBindings0 => eq0_m; rewrite FO.fold_Empty //=.
  by apply: eqarefl; apply: rAE.
case/FO.IsBindingsS=> [sm]; set m' := FO.MO.add _ _ _ => -[? eqm].
have: rA (fold f m x0) (fold f m' x0).
- apply: FO.fold_Equal => //.
move/(eqatrans rAE) => + hbds; apply; rewrite {m eqm}/m'.
rewrite (FO.fold_add _ fP) //=.
exact/fcomp/ih.
Qed.

End MapFold.
