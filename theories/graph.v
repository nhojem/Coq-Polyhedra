Require Import Recdef.
From mathcomp Require Import all_ssreflect all_algebra finmap.
(* Require Import extra_misc inner_product extra_matrix xorder vector_order row_submx vector_order.
Require Import hpolyhedron polyhedron barycenter poly_base.
 *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require BinNums FMapAVL FSetAVL.
Require Import OrderedType.

Definition seq := seq.seq.

Module Type Label.
Parameter t : Type.
End Label.

Module Graph (O : OrderedType) (L : Label).

Module Map := FMapAVL.Make(O).
Module FSet := FSetAVL.Make(O).

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

End Defs.

Section Predicates.
Inductive path x y (G : t) : Prop :=
  |C z of (mem_edge x z G) & path z y G : path x y G
  |R of (O.eq x y): path x y G.

Definition connected (G : t) := forall x y, path x y G.

(* Lemma foo x y (G : t) : mem_edge x y G -> path x y G.
Proof.
by move=> edge; apply: (C edge); apply: R.
Qed.
*)

End Predicates.
End Graph.


