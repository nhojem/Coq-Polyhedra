Require Import Recdef.
From mathcomp Require Import all_ssreflect all_algebra finmap.
Require Import extra_misc inner_product extra_matrix xorder vector_order row_submx vector_order.
Require Import hpolyhedron polyhedron barycenter poly_base.

Require Import BinNums FMapPositive.

Import Order.Theory.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope poly_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Misc.
Fixpoint b_to_p (s : bitseq) : positive :=
  if s is h::t then
    if h is true then xI (b_to_p t) 
    else xO (b_to_p t)
  else xH.

Fixpoint p_to_b (p : positive) :=
  match p with
    |xI p' => true :: (p_to_b p')
    |xO p' => false :: (p_to_b p')
    |xH => [::]
  end.

Fixpoint map_of_bitseq_aux (s: seq bitseq) (m : PositiveMap.t nat) :=
  if s is h::t then
    let x := (b_to_p h) in
    if PositiveMap.find x m is Some n then
      map_of_bitseq_aux t (PositiveMap.add x (S n)%nat m)
    else map_of_bitseq_aux t (PositiveMap.add x (1%nat) m)
  else m.

Definition map_of_bitseq (s : seq bitseq) :=
  map_of_bitseq_aux s (PositiveMap.empty nat).

End Misc.

Section Algorithm.
Context (L U: Type) (dft : L).
(* L is the type of linear equations, U is a vector space*)
Context (Po : seq L).

Context (sat_ineq sat_eq sat_eq0: L -> U -> bool).


Definition sat_Po (x : U) :=
  all (fun e => sat_ineq e x) Po.
Definition mask_eq (m : bitseq) (x : U):=
  all (fun e => sat_eq e x) (mask m Po).
Definition nth_eq0 (m : nat) (x : U) :=
  sat_eq0 (nth dft Po m) x.
Definition mask_eq0 (m: bitseq) (x : U):=
  all (fun e => sat_eq0 e x) (mask m Po).

Definition vertex := (bitseq * U)%type.
Definition edge := (bitseq * U * bitseq * bitseq)%type.

Definition vertex_mask (v : vertex) := v.1.
Definition vertex_point (v : vertex) := v.2.
Definition edge_mask (e : edge) := e.1.1.1.
Definition edge_norm (e : edge) := e.1.1.2.
Definition edge_fst (e : edge) := e.1.2.
Definition edge_snd (e : edge) := e.2.

Definition mask_incident (s:bitseq) :=
  let fix aux temp cur res :=
    if cur is h::t then
      if h is true then
        aux (rcons temp h) t (((rcons temp false) ++ t)::res)
        else aux (rcons temp h) t res
    else res
  in aux [::] s [::].

Fixpoint mask_cardinal (s:bitseq) :=
  if s is h::t then
    if h is true then (S (mask_cardinal t)) else mask_cardinal t
  else 0%nat.

Definition vtx_incident_edges (v : vertex) (E : seq edge) :=
  let: (m, _) := v in
  let incidents := mask_incident m in
  let fix aux mas (l : seq edge) :=
    if l is h::t then
      let: (medge, _, medge1, medge2) := h in
      if ((mas == medge) && (xorb (m == medge1) (m == medge2))) then
        Some medge else aux mas t
    else None
  in map (fun mas => aux mas E) incidents.

(* For each vertex v and edge list E, vtx_incident_edges v E returns a seq (option bitseq), such that (Some m) means that m is an incident edge of v, m is in E and v is one of the two vertices associated to m*)
  

Definition bipartite (V : seq vertex) (E : seq edge) :=
  let incidents := map (fun v => vtx_incident_edges v E) V in
  let incident_couples := zip V incidents in
  if all (fun c => (mask_cardinal c.1.1 == size c.2) && (~~ (None \in c.2))) incident_couples then
  (*Here, every vertex have n correct incident edges*)
    let edges_visited := pmap id (flatten incidents) in
    let edges_map := map_of_bitseq edges_visited in
    all (fun c => c.2 == 2) (PositiveMap.elements edges_map) 
  else false.

(* Test *)

(*
  Parameter (d : U).
  Definition v1 : vertex :=
    ([:: true; false; true; false], d).
  Definition v2 : vertex :=
    ([:: true; false; false; true], d).
  Definition v3 : vertex :=
    ([:: false; true; false; true], d).
  Definition v4 : vertex :=
    ([:: false; true; true; false], d).

  Definition ma1 := [:: true; false; false; false].
  Definition ma2 := [:: false; true; false; false].
  Definition ma3 := [:: false; false; true; false].
  Definition ma4 := [:: false; false; false; true].
  
  Definition edges : seq edge :=
    [::
      (ma1, d, [:: true; false; true; false], [:: true; false; false; true]);
      (ma2, d, [:: false; true; true; false], [:: false; true; false; true]);
      (ma3, d, [:: true; false; true; false], [:: false; true; true; false]);
      (ma4, d, [:: true; false; false; true], [:: false; true; false; true])
  ].

  Definition vertices := [:: v1; v2; v3; v4].
  

  Compute bipartite vertices edges.

*)

(* TODO : pour tout sommet,
chaque arête incidente est dans la liste des arêtes; et pour chacune de ces arêtes incidentes, on vérifie que le sommet est bien l'un des deux sommets associés à l'arête.
Et chaque arête aura été visitée deux fois exactement durant le processus*)

Fixpoint vtx_consistent (V : seq vertex) :=
  if V is h::t then
   let: (m,p) := h in
    [&& sat_Po p, mask_eq m p & vtx_consistent t]
  else true.

Fixpoint edge_consistent (E : seq edge) :=
  if E is h::t then
    let: (m,d,m1,m2) := h in
    [&& mask_eq0 m d, ~~ mask_eq0 m1 d, ~~mask_eq0 m2 d & edge_consistent t]
  else true.

Definition algorithm (V : seq vertex) (E : seq edge) :=
  [&& bipartite V E, vtx_consistent V & edge_consistent E].


End Algorithm.

Section TestCarre.

Context (R := rat) (L := ((seq R) * R)%type) (U := seq R).

Definition e1 : L := ([:: -1; 0], 0).
Definition e2 : L := ([:: 1; 0], 1).
Definition e3 : L := ([:: 0; -1], 0).
Definition e4 : L := ([:: 0; 1], 1).

Definition Po := [:: e1; e2; e3; e4].
Definition ma1 := [:: true; false; false; false].
Definition ma2 := [:: false; true; false; false].
Definition ma3 := [:: false; false; true; false].
Definition ma4 := [:: false; false; false; true].

Definition d1 : U := [:: 0; 1].
Definition d2 : U := [:: 0; -1].
Definition d3 : U := [:: 1; 0].
Definition d4 : U := [:: -1; 0].

Definition edges : seq (edge U) :=
    [::
      (ma1, d1, [:: true; false; true; false], [:: true; false; false; true]);
      (ma2, d2, [:: false; true; true; false], [:: false; true; false; true]);
      (ma3, d3, [:: true; false; true; false], [:: false; true; true; false]);
      (ma4, d4, [:: true; false; false; true], [:: false; true; false; true])
  ].


Definition v1 : vertex U :=
  ([:: true; false; true; false], [:: 0; 0]).
Definition v2 : vertex U :=
  ([:: true; false; false; true], [:: 0; 1]).
Definition v3 : vertex U :=
  ([:: false; true; false; true], [:: 1; 1]).
Definition v4 : vertex U :=
  ([:: false; true; true; false], [:: 1; 0]).

Definition vertices := [:: v1; v2; v3; v4].


Fixpoint test_dot (x y : U) :=
  if (x, y) is (x'::tx, y'::ty) then
    x' * y' + test_dot tx ty
  else 0. 

Definition sat_ineq (e: L) (x : U) :=
  (test_dot e.1 x) <= e.2.

Definition sat_eq (e: L) (x : U) :=
  (test_dot e.1 x) == e.2.

Definition sat_eq0 (e: L) (x : U) :=
  (test_dot e.1 x) == 0.

Eval vm_compute in bipartite vertices edges.
Eval vm_compute in vtx_consistent Po sat_ineq sat_eq vertices.
Eval vm_compute in edge_consistent Po sat_eq0 edges.
Eval vm_compute in algorithm Po sat_ineq sat_eq sat_eq0 vertices edges.


End TestCarre.