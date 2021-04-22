Require Import Recdef.
Require Import FMaps FMapAVL FSetAVL.
From mathcomp Require Import all_ssreflect all_algebra finmap.
Require Import MapFold.

(* Require Import extra_misc inner_product extra_matrix xorder vector_order row_submx vector_order.
Require Import hpolyhedron polyhedron barycenter poly_base.
 *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Open Scope order_scope.
Import Order.Theory.

Definition seq := seq.seq.

Module Type Label.
Parameter t : Type.
End Label.

Module Graph (O : Sig) (L : Label).

Module MF := MapFold O.
Module Map := MF.MO.
Module Keys := Map.OT.
Module FSet := FSetAVL.Make(Keys).

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

Definition adj_list (G : t) := Map.elements G.
Definition vertex_list (G : t) := (unzip1 (Map.elements G)).

End Defs.

Section Lemmas.

Lemma adj_listP (G : t) : Map.IsBindings G (adj_list G).
Proof.
Admitted.

Section VertexFold.


Lemma vertex_foldE A f rA (G : t) (a:A) vtxs:
  `{Equivalence rA} ->
  MF.fP_d f rA -> MF.fC_d f rA -> MF.fcomp_d f rA ->
  Map.IsBindings G vtxs ->
  rA (vertex_fold f G a) (foldr (fun kv x0 => f kv.1 kv.2 x0) a vtxs).
Proof. exact: MF.L. Qed.



Lemma vertex_allE f rA (G:t) vtxs:
  `{Equivalence rA} ->
  (forall a b c d, rA a b -> rA (a && (f c d)) (b && (f c d))) -> 
  Map.IsBindings G vtxs ->
  rA (vertex_all f G) (all (fun x => f x.1 x.2) vtxs).
Proof.
move=> rAE fP bind_vtxs.
apply: (eqatrans rAE (vertex_foldE _ _ _ _ _ bind_vtxs)) => //.
- move => ?? -> ?? -> ??; exact: fP.
- move=> ?????; rewrite andbAC; apply/fP/fP/(eqarefl rAE).
- move=> ????; exact: fP.
- elim: vtxs {bind_vtxs} => //=; first exact: (eqarefl rAE).
  by move=> a l ih; rewrite [in X in rA _ X]andbC; apply/fP/ih.
Qed.

Lemma vertex_fold_eq A f (G : t) (a : A) vtxs:
  Map.IsBindings G vtxs ->
  MF.fC_d f eq ->
  (vertex_fold f G a) = (foldr (fun kv x0 => f kv.1 kv.2 x0) a vtxs).
Proof.
move=> ??; apply: vertex_foldE => //.
- by move=> ?? -> ?? -> ?? ->.
- by move=> ???? ->.
Qed.

Lemma vertex_all_eq f (G : t) vtxs:
  Map.IsBindings G vtxs ->
  (vertex_all f G) = (all (fun x => f x.1 x.2) vtxs).
Proof. by move=> ?; apply: vertex_allE => //; move=> ???? ->. Qed.

Lemma vertex_fold_eq_key A (f : Map.key -> A -> A) (G : t) a vtxs:
  perm_eq vtxs (vertex_list G) ->
  (forall p q a', (f p (f q a')) = (f q (f p a'))) ->
  (vertex_fold (fun k _ x => f k x) G a) = foldr f a vtxs.
Proof.
Admitted.



End VertexFold.



End Lemmas.

End Graph.


