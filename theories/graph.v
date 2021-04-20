Require Import Recdef.
From mathcomp Require Import all_ssreflect all_algebra finmap.
(* Require Import extra_misc inner_product extra_matrix xorder vector_order row_submx vector_order.
Require Import hpolyhedron polyhedron barycenter poly_base.
 *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require BinNums FMapAVL FSetAVL.
Require Import OrderedType OrderedTypeEx.

Definition seq := seq.seq.

Module Type Label.
Parameter t : Type.
End Label.

Module Graph (U : UsualOrderedType) (L : Label).

Module OrderedEqType (Us : UsualOrderedType).

Definition eq_mixin := comparableMixin Us.eq_dec.
Canonical t := EqType Us.t eq_mixin.

End OrderedEqType.

Module O := OrderedEqType U.
Module Map := FMapAVL.Make(U).
Module FSet := FSetAVL.Make(U).

Section Defs.

Definition t := Map.t (L.t * FSet.t).

Definition add_vertex v label (G : t) :=
  if Map.mem v G then G else Map.add v (label, FSet.empty) G.

Definition add_vertices s (G : t) :=
  let f x G := let: (v,l) := x in add_vertex v l G in
  foldr f G s.

Definition find_vertex v (G : t) := Map.find v G.

Definition add_edge v1 v2 (G : t) :=
  if find_vertex v1 G is Some (l1, s1) then
    if find_vertex v2 G is Some (l2, s2) then
      let G' := Map.add v1 (l1, FSet.add v2 s1) G in
      Map.add v2 (l2, FSet.add v1 s2) G'
    else G else G.

Definition add_edges s (G : t) :=
  let f x G := let: (v1,v2) := x in add_edge v1 v2 G in
  foldr f G s.

Definition neighbours v (G : t) :=
  if Map.find v G is Some (l,s) then Some s else None.

Definition label v (G : t) :=
  if Map.find v G is Some (l,s) then Some l else None.

Definition empty := Map.empty (L.t * FSet.t).

Definition is_empty (G : t) := Map.is_empty G.

Definition nb_vertices (G : t) := Map.cardinal G.

Definition nb_neighbours v (G : t) :=
  if neighbours v G is Some s then Some (FSet.cardinal s) else None.

Definition mem_vertex v (G : t) := Map.mem v G.

Definition mem_edge v1 v2 (G : t) :=
  if Map.find v1 G is Some (_,s) then FSet.mem v2 s else false.

Definition vertex_fold (A : Type) f (G : t) (a : A) :=
  Map.fold f G a.
  
Definition neighbour_fold (A: Type) f v (G : t) (a : A) :=
  if neighbours v G is Some s then FSet.fold f s a else a.

Definition vertex_all f G :=
  vertex_fold (fun k d b => b && f k d) G true.

Definition neighbour_all f G v :=
  neighbour_fold (fun k b => b && f k) v G true.

Definition vertex_list (G : t) : seq O.t := unzip1 (Map.elements G).

Definition remove_vertex v (G : t) := Map.remove v G.

Lemma vertex_listP (G : t) x :
  x \in vertex_list G = mem_vertex x G.
Proof.
Admitted.

Lemma vtx_list_uniq (G : t): uniq (vertex_list G).
Proof.
Admitted.

Lemma vtx_list_remove G v :
  mem_vertex v G ->
  perm_eq (vertex_list G) (v :: vertex_list (remove_vertex v G)).
Proof.
Admitted.

Fixpoint is_correct_list (G : t) (vs : seq (O.t * _)) :=
  if vs is h::tl then
  (find_vertex h.1 G = Some h.2) /\ (is_correct_list G tl) else
  True.

Lemma is_correct_list_rem (G : t) vs (v : O.t) :
  mem_vertex v G -> is_correct_list G vs ->
  is_correct_list (remove_vertex v G) [seq x <- vs | x.1 != v].
Proof.
Admitted.

Lemma is_correct_listP (G : t):
  is_correct_list G (Map.elements G).
Proof.
move: (@Map.elements_2 _ G).
elim: (Map.elements G) => // a l HI corr /=; split.
- rewrite /find_vertex; exact/Map.find_1/corr/InA_cons_hd.
- apply/HI => x e in_x; exact/corr/InA_cons_tl.
Qed.

Fixpoint rem_vertex (T : Type) v (s : seq (O.t * T)) := match s with
  |h::t => if h.1 == v then t else (h::(rem_vertex v t))
  |[::] => [::]
end.

Lemma elements_rem G (v : O.t):
  Map.elements (remove_vertex v G) =
  rem_vertex v (Map.elements G).
Proof.
Admitted.

(* Lemma uniq_elements G (v : O.t):
  size (rem_vertex v (Map.elements G)) >= *)


Lemma foo (A : Type) f (k : O.t) d (G : t) (x0 : A) :
  find_vertex k G = Some d ->
  (forall k1 d1 k2 d2 a, f k1 d1 (f k2 d2 a) = f k2 d2 (f k1 d1 a)) ->
  vertex_fold f G x0 = f k d (vertex_fold f (remove_vertex k G) x0).
Proof.
rewrite /find_vertex /vertex_fold !Map.fold_1 elements_rem.
move=> k_map fAC.
move:(Map.find_2 k_map) => maps_to.
move:(Map.elements_1 maps_to) (@Map.elements_3w _ G) x0.
elim : (Map.elements G); first by rewrite InA_nil.
move=> a l HI /= /InA_cons [].
+ case => /= <- <- _ ?; rewrite eq_refl /=.
  suff ->: forall s x0, fold_left (fun a0 p => f p.1 p.2 a0) s (f k d x0) =
  f k d (fold_left (fun a0 p => f p.1 p.2 a0) s x0) by [].
  by elim => // hs ts HI_have x1 /=; rewrite -HI_have fAC.
+ move=> inl nodup_al.
  have ->: ((a.1 == k :> O.t) = false).
  - admit.
  move=> x0 /=; rewrite HI //.
  rewrite -(@app_nil_l _ (a::l)) in nodup_al.
  exact: (NoDupA_split nodup_al).
Admitted.

Lemma vertex_foldE (A : Type) f G (x0 : A) vs:
  perm_eq (unzip1 vs) (vertex_list G)
  -> is_correct_list G vs
  -> (forall a k d k' d', f k d (f k' d' a) = f k' d' (f k d a))
  -> vertex_fold f G x0 =
  foldr (fun x a => f x.1 x.2 a) x0 vs.
Proof.
elim: vs G => [|a l HI].
- move=> G /=; rewrite perm_sym /vertex_fold Map.fold_1.
  by move/perm_nilP/map_eq_nil => -> /=.
- case: a => k d /= G perm_G.
  have k_vtx : mem_vertex k G.
  + move: (perm_mem perm_G) => /(_ k) /esym.
    by rewrite inE eq_refl /= vertex_listP.
  move/(perm_trans perm_G) : (vtx_list_remove k_vtx).
  rewrite perm_cons => perm_l.
  case => find_vtx; move/(is_correct_list_rem k_vtx).
  have ->: [seq x <- l | x.1 != k] = l.
  + apply/all_filterP; rewrite -(@all_map _ _ fst (fun x => x != k)).
    apply/allP => x x_l; move: (perm_uniq perm_G).
    rewrite vtx_list_uniq cons_uniq => /andP [+ _].
    by apply/contra; move/eqP => <-.
  move=> corr_l fAC; rewrite -(HI _ perm_l corr_l fAC).
  exact: foo.
Qed.
  
 




Lemma key_foldE (A : Type) f G (x0 : A) (vs : seq (O.t)):
  uniq vs
  -> (forall x, x \in vs = mem_vertex x G)
  -> (forall a k k', f (f a k) k' = f (f a k') k)
  -> vertex_fold (fun k _ a => f a k) G x0 =
    foldr (fun x a => f a x) x0 vs.
Proof.
Admitted.

End Defs.

(* Section Predicates.
Inductive path x y (G : t) : Prop :=
  |C z of (mem_edge x z G) & path z y G : path x y G
  |R of (O.eq x y): path x y G.

Definition connected (G : t) := forall x y, path x y G.

(* Lemma foo x y (G : t) : mem_edge x y G -> path x y G.
Proof.
by move=> edge; apply: (C edge); apply: R.
Qed.
*)

End Predicates. *)
End Graph.


