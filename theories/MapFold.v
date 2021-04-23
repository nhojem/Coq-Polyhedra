(* -------------------------------------------------------------------- *)
(* ------- *) Require Import FMaps FMapAVL.
From mathcomp Require Import all_ssreflect.
Require Import Classes.RelationClasses.

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

  Definition all {U} f (m : t U) :=
    fold (fun k d b => b && f k d) m true.

End M.

Module MapFold (O : Sig).
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

Lemma IsBindingsP {U} (m : MO.t U):
  MO.IsBindings m (MO.elements m).
Proof.
split => // k; rewrite elements_o; elim: (MO.elements m) => //= a l ih.
case: a => a1 a2 /=; case/boolP: (a1 == k).
- by move/eqP => -> /=; apply/ifT; rewrite /eqb; case: (eq_dec k k).
- rewrite eq_sym -ih => /eqP kna1; apply: ifF.
  by rewrite /eqb; case: (eq_dec k a1).
Qed.


Lemma makeBinding {U} (m: MO.t U) keys:
  perm_eq keys (unzip1 (MO.elements m)) ->
  exists2 l, unzip1 l = keys & MO.IsBindings m l.
Proof.
elim: keys m => //=.
- move=> m; rewrite perm_sym; move/perm_nilP/(congr1 size) => /=.
  rewrite size_map; case E: (MO.elements m) => // _.
  exists [::] => //; split; rewrite ?E //=.
  by move=> ?; rewrite F.elements_o E.
- move => a l ih m perm_al.
  have: perm_eq l (unzip1 (MO.elements (MO.remove a m))).
  + move:(perm_uniq perm_al); rewrite uniq_keys cons_uniq => /andP [anl uniql].
    apply: uniq_perm; rewrite ?uniq_keys //.
    move=> x; apply/idP/inkeysP.
    - move=> xl; rewrite F.remove_neq_in_iff.
        by apply/inkeysP; rewrite -(perm_mem perm_al) inE xl orbT.
      by apply/eqP; apply/contraNneq: anl => ->.
    - case/F.remove_in_iff => /eqP + /inkeysP.
      rewrite -(perm_mem perm_al) in_cons eq_sym.
      by case: (x == a).
  case/ih => L unzip_L bind_L.
  move: (perm_mem perm_al)=> /(_ a) /eqP.
  rewrite eq_sym in_cons eq_refl /= => /eqP/inkeysP/F.elements_in_iff.
  case => e elt_ae; move: (MO.find_1 (MO.elements_2 elt_ae)) => find_ae.
  exists ((a,e) :: L); last split; rewrite /= ?unzip_L //.
  move=> k; case/boolP: (a==k).
  + by move=> /eqP <- /=.
  + by move/eqP => ?; case: bind_L => _ /(_ k) <-; rewrite F.remove_neq_o.
Qed.

Section Fold. 
(* -------------------------------------------------------------------- *)


Definition fP_d {T U A} (f : T -> U -> A -> A) rA :=
  `{Proper (eq ==> eq ==> rA ==> rA) f}.

Definition fC_d {T U A} (f : T -> U -> A -> A) (rA : A -> A -> Prop)  :=
  forall k1 v1 k2 v2 a, rA (f k1 v1 (f k2 v2 a)) (f k2 v2 (f k1 v1 a)).

Definition fcomp_d {T U A} (f : T -> U -> A -> A) (rA : A -> A -> Prop) :=
  forall k v a1 a2, rA a1 a2 -> rA (f k v a1) (f k v a2).

Lemma L {U A} (f : MO.key -> U -> A -> A) rA m x0 bds :
  `{Equivalence rA} ->
  fP_d f rA -> fC_d f rA -> fcomp_d f rA ->
  MO.IsBindings m bds ->
  rA (MO.fold f m x0) (foldr (fun kv a => f kv.1 kv.2 a) x0 bds).
Proof.
move=> rAE fP fC fcomp.
elim: bds m => [|bd bds ih] m.
- move/IsBindings0 => eq0_m; rewrite fold_Empty //=.
  by apply: eqarefl; apply: rAE.
case/IsBindingsS=> [sm]; set m' := MO.add _ _ _ => -[? eqm].
have: rA (MO.fold f m x0) (MO.fold f m' x0).
- apply: fold_Equal => //.
move/(eqatrans rAE) => + hbds; apply; rewrite {m eqm}/m'.
rewrite (fold_add _ fP) //=.
exact/fcomp/ih.
Qed.

Lemma L_all {U} (f : MO.key -> U -> bool) rA m bds :
  `{Equivalence rA} ->
  (forall a b c d, rA a b -> rA (a && (f c d)) (b && (f c d))) -> 
  MO.IsBindings m bds ->
  rA (MO.all f m) (all (fun x => f x.1 x.2) bds).
Proof.
move=> rAE fP bind_bds; apply: (eqatrans rAE (L _ _ _ _ _ bind_bds)) => //.
- move=> ?? -> ?? -> ??; exact: fP.
- move=> ?????; rewrite andbAC; exact/fP/fP/(eqarefl rAE).
- move=> ????; exact: fP.
- elim: bds {bind_bds} => //=; first exact: (eqarefl rAE).
  move=> a l ih; rewrite [in X in rA _ X]andbC; exact/fP/ih.
Qed.

Lemma L_key {U A} (f : MO.key -> A -> A) rA (m : MO.t U) bds x0:
  `{Equivalence rA} ->
  `{Proper (eq ==> rA ==> rA) f} ->
  (forall k k' a, rA (f k (f k' a)) (f k' (f k a))) ->
  (forall k a a', rA a a' -> rA (f k a) (f k a')) ->
  perm_eq bds (unzip1 (MO.elements m)) ->
  rA (MO.fold (fun k _ a => f k a) m x0) (foldr f x0 bds).
Proof.
move=> rAE fP fC fcomp perm_bds.
case: (makeBinding perm_bds) => B unzip_B bind_B.
apply: (eqatrans rAE (L _ rAE _ _ _ bind_B)).
- move=> ?? -> _ _ _ ??; exact: fP.
- move=> ?????; exact: fC.
- move=> ????; exact: fcomp.
- rewrite -{}unzip_B; elim: B {bind_B}; first exact: (eqarefl rAE).
  move=> a l ih /=; exact/fcomp/ih.
Qed.

End Fold.

End MapFold.
