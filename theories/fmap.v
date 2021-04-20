From mathcomp Require Import all_ssreflect.
(* ------- *) Require Import FMaps FMapAVL.

Open Scope order_scope.

Import Order.Theory.

(* -------------------------------------------------------------------- *)
Context {d : unit} (T : orderType d).

Module OType <: OrderedType.
Definition t : Type := T.

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
Module M.
  Include FMapAVL.Make(OType).

  Definition IsBindings {U} (m : t U) (bds : seq.seq (T * U)) :=
    [/\ perm_eq (unzip1 bds) (unzip1 (elements m))
      & forall k, find k m = ohead [seq kv.2 | kv <- bds & kv.1 == k]].
End M.

Module F.
  Include FMapFacts.Facts(M).
End F.

Notation fmap := M.t.

(* -------------------------------------------------------------------- *)
Context (U A : Type) (f : T -> U -> A -> A) (rA : A -> A -> Prop).

Axiom rAE : `{Equivalence rA}.

Axiom fC : forall k1 v1 k2 v2 a,
  rA (f k1 v1 (f k2 v2 a)) (f k2 v2 (f k1 v1 a)).

Axiom rA_comp : forall k1 k2 x y,
  rA x y -> rA (f k1 k2 x) (f k1 k2 y).
(*Axiome nécessaire ?*)

Lemma foo l1 l2 a y:
  rA (fold_left (fun a0 p => f p#1 p#2 a0) (l1 ++ ((a#1, a#2) :: l2)) y)
  (f a.1 a.2 (fold_left (fun a0 p => f p#1 p#2 a0) (l1 ++ l2) y)).
Proof. Admitted.



Lemma L m x0 bds : M.IsBindings m bds ->
  rA (M.fold f m x0) (foldr (fun kv a => f kv.1 kv.2 a) x0 bds).
Proof.
rewrite M.fold_1 /M.IsBindings; case.
Search _ M.elements.
move: (F.elements_mapsto_iff m).
elim: bds m (M.elements m).
- move=> ??? /=; rewrite perm_sym; move/perm_nilP/map_eq_nil => -> ? /=.
  exact: (eqarefl rAE).
- move=> /= a l HI m elt map_elt perm_elt assoc.
  move: (assoc a.1); rewrite eq_refl /= => map_a.
  move: (M.find_2 map_a) => /map_elt InA_a.
  case: (InA_split InA_a) => l1 [[k1 k2]] [l2] [[]] /= <- <- ->.
  apply: (eqatrans rAE (foo l1 l2 a x0)).
  apply/rA_comp/(@HI (M.remove a.1 m)); first (move=> x y; split).
  + admit.
  + admit.
  + admit.
  + admit.
Admitted.
  





- move=> ?? [] /=; rewrite perm_sym; move/perm_nilP/map_eq_nil => -> ? /=.
  exact: (eqarefl rAE).
- move=> /= a l HI x0 m [] perm_elt assoc.
  move: (assoc a.1); rewrite eq_refl /= F.elements_o.
  move/findA_NoDupA => /(_ (M.elements_3w m)) a_in_elt.
  case: (InA_split a_in_elt) => l1 [k [l2]] [] /= [].
  case: k => /= ?? <- <- elt_cat.
  move: perm_elt; rewrite elt_cat.
  Search _ perm_eq.
  have: perm_eq l (l1++l2).
  



Lemma l2 m1 m2 x0 : M.Equal m1 m2 -> rA (M.fold f m1 x0) (M.fold f m2 x0).
Proof. Admitted.