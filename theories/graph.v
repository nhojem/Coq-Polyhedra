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

Definition t := Map.t (L.t * FSet.t).

Definition add_vertex v label (G : t) :=
  if Map.mem v G then G else Map.add v (label, FSet.empty) G.

Definition add_vertices s (G : t) :=
  let f x G := let: (v,l) := x in add_vertex v l G in
  foldr f G s.

Definition add_edge v1 label1 v2 label2 (G : t) :=
  let G' :=
    if Map.find v1 G is Some (l,s) then Map.add v1 (l, FSet.add v2 s) G
    else Map.add v1 (label1, FSet.singleton v2) G
  in if Map.find v2 G' is Some (l,s) then Map.add v2 (l, FSet.add v1 s) G'
  else Map.add v2 (label2, FSet.singleton v1) G'.

Definition add_edges s (G : t) :=
  let f x G := let: (v1,l1,v2,l2) := x in add_edge v1 l1 v2 l2 G in
  foldr f G s.

Definition neighbours v (G : t) :=
  if Map.find v G is Some (l,s) then Some s else None.

Definition label v (G : t) :=
  if Map.find v G is Some (l,s) then Some l else None.

Definition empty := Map.empty.

Definition is_empty (G : t) := Map.is_empty G.

Definition nb_vertices (G : t) := Map.cardinal G.

Definition nb_neighbours v (G : t) :=
  if neighbours v G is Some s then Some (FSet.cardinal s) else None.

Definition mem_vertex v (G : t) := Map.mem v G.

Definition mem_edge v1 v2 (G : t) :=
  if Map.find v1 G is Some (_,s) then FSet.mem v2 s else false.

Definition find_vertex v (G : t) := Map.find v G.

End Graph.

