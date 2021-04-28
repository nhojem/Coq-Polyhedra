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
Module FSet := MF.FSet.

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
Definition neighbour_list (G : t) v :=
  oapp FSet.elements [::] (neighbours v G).

End Defs.

Section Lemmas.

Lemma adj_listP (G : t) : Map.IsBindings G (adj_list G).
Proof. exact: MF.IsBindingsP. Qed.

Lemma uniq_vtx_list (G : t) : uniq (vertex_list G).
Proof. exact: MF.uniq_keys. Qed.

Lemma vtx_mem_list (G : t) v :
  v \in vertex_list G = mem_vertex v G.
Proof.
apply/(sameP idP)/(iffP idP).
- move/MF.mem_in_iff => ?; exact/MF.inkeysP.
- move/MF.inkeysP => ?; exact/MF.mem_in_iff.
Qed.

Lemma edge_mem_list (G : t) v1 v2:
  mem_edge v1 v2 G = (v2 \in neighbour_list G v1).
Proof.
rewrite /neighbour_list /neighbours /mem_edge.
case: (Map.find v1 G) => //; case => _ a /=.
apply/(sameP idP)/(iffP idP).
- by move/MF.infsetP/FSet.mem_1.
- by move/FSet.mem_2/MF.infsetP.
Qed.

Lemma vtx_memE (G : t) v:
  mem_vertex v G <-> (exists e, find_vertex v G = Some e).
Proof.
split.
- case/Map.mem_2/MF.elements_in_iff => e ina.
  by move: (Map.find_1 (Map.elements_2 ina)) => ?; exists e.
- rewrite /find_vertex; case=> e find_vtx; apply/Map.mem_1/MF.in_find_iff.
  by rewrite find_vtx.
Qed.

Lemma find_mem (G : t) v e:
  find_vertex v G = Some e -> mem_vertex v G.
Proof. by rewrite /mem_vertex MF.mem_find_b /find_vertex => ->. Qed.

Lemma uniq_neighbour_list (G : t) v:
  uniq (neighbour_list G v).
Proof.
rewrite /neighbour_list; case: (neighbours v G)=> //= S.
exact: MF.uniq_fset.
Qed.

Lemma nb_neighbours_list (G : t) v:
  mem_vertex v G ->
  nb_neighbours v G = Some (size (neighbour_list G v)).
Proof.
rewrite /nb_neighbours /neighbour_list /neighbours.
case/Map.mem_2/MF.elements_in_iff; case => a b ina.
move: (Map.find_1 (Map.elements_2 ina)) => -> /=.
congr Some; exact: FSet.cardinal_1.
Qed.

Lemma nb_neighboursF (G : t) v:
  ~~ mem_vertex v G ->
  nb_neighbours v G = None.
Proof.
rewrite -vtx_mem_list; move/MF.inkeysP; rewrite /nb_neighbours /neighbours.
by move/MF.not_find_in_iff => ->.
Qed.

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
Proof. exact: MF.L_all. Qed. 

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

Lemma vertex_allP (f : Map.key -> L.t * FSet.t -> bool)  (G:t):
  reflect (forall v e, find_vertex v G = Some e -> f v e) (vertex_all f G).
Proof. exact: MF.L_allP. Qed.

Lemma vertex_fold_key {A} rA (f : Map.key -> A -> A) (G : t) a vtxs:
  `{Equivalence rA} ->
  `{Proper (eq ==> rA ==> rA) f} ->
  (forall k k' a, rA (f k (f k' a)) (f k' (f k a))) ->
  (forall k a a', rA a a' -> rA (f k a) (f k a')) ->
  perm_eq vtxs (vertex_list G) ->
  rA (vertex_fold (fun k _ x => f k x) G a) (foldr f a vtxs).
Proof. exact: MF.L_key. Qed.

Lemma vertex_fold_eq_key {A} (f : Map.key -> A -> A) (G : t) a vtxs:
  (forall k k' a, (f k (f k' a)) = (f k' (f k a))) ->
  perm_eq vtxs (vertex_list G) ->
  vertex_fold (fun k _ x => f k x) G a = foldr f a vtxs.
Proof. by move=> ??; apply: vertex_fold_key => // ??? ->. Qed.

Lemma neighbour_foldE {A} rA (f : Map.key -> A -> A) (G : t) a neis v:
  mem_vertex v G ->
  `{Equivalence rA} ->
  `{Proper (eq ==> rA ==> rA) f} ->
  (forall k k' a, rA (f k (f k' a)) (f k' (f k a))) ->
  (forall k a a', rA a a' -> rA (f k a) (f k a')) ->
  perm_eq neis (neighbour_list G v) ->
  rA (neighbour_fold f v G a) (foldr f a neis).
Proof.
rewrite /neighbour_list.
case/Map.mem_2/MF.elements_in_iff; case => l s ina.
move: (Map.find_1 (Map.elements_2 ina)).
rewrite /neighbour_fold /neighbours => -> /= rAE fP fC fcomp perm_neis.
exact: MF.fsetL.
Qed.

Lemma neighbour_fold_eq {A} (f : Map.key -> A -> A) (G : t) a neis v:
  mem_vertex v G ->
  (forall k k' a, (f k (f k' a)) = (f k' (f k a))) ->
  perm_eq neis (neighbour_list G v) ->
  neighbour_fold f v G a = foldr f a neis.
Proof. by move=> ???; apply: neighbour_foldE => // ??? ->. Qed.

Lemma neighbour_foldF {A} (f : Map.key -> A -> A) (G : t) a v:
  ~~ mem_vertex v G -> neighbour_fold f v G a = a.
Proof.
rewrite /neighbour_fold /neighbours.
case E: (mem_vertex v G) => // _.
by move/MF.not_mem_in_iff/MF.not_find_in_iff: E => ->.
Qed.

Lemma neighbour_allF f (G : t) v:
  ~~ mem_vertex v G -> neighbour_all f G v = true.
Proof. exact: neighbour_foldF. Qed.

Lemma neighbour_allE rA (f : Map.key -> bool) (G : t) neis v:
  mem_vertex v G ->
  `{Equivalence rA} ->
  (forall a b c, rA a b -> rA (a && (f c)) (b && (f c))) ->
  perm_eq neis (neighbour_list G v) ->
  rA (neighbour_all f G v) (all f neis).
Proof.
move=> ? rAE fP perm_neis; rewrite /neighbour_all.
apply: (eqatrans rAE (neighbour_foldE _ _ _ _ _  _ perm_neis)) => //.
- move=> ?? -> ??; exact: fP.
- move=> ???; rewrite andbAC; apply/fP/fP; exact: (eqarefl rAE).
- move=> ???; exact: fP.
- elim: neis {perm_neis}.
  + exact: (eqarefl rAE).
  + move=> a l ih /=; rewrite [X in rA _ X]andbC; exact/fP/ih.
Qed.

Lemma neighbour_all_eq (f: Map.key -> bool) (G : t) neis v:
  mem_vertex v G ->
  perm_eq neis (neighbour_list G v) ->
  neighbour_all f G v = all f neis.
Proof. by move=> ??; apply: neighbour_allE => // ??? ->. Qed. 

  
End VertexFold.

End Lemmas.
End Graph.


