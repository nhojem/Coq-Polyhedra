Require Import Recdef.
From mathcomp Require Import all_ssreflect all_algebra finmap.
Require Import extra_misc inner_product extra_matrix xorder vector_order row_submx vector_order.
Require Import hpolyhedron polyhedron barycenter poly_base.

Import Order.Theory.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope poly_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Algorithm.
Context {R : realFieldType} {n : nat}.
Context (Po : seq lrel[R]_n).

Definition sat_ineq (e : lrel[R]_n) (x : 'cV[R]_n) :=
  '[e.1, x] <= e.2.
Definition sat_eq (e : lrel[R]_n) (x : 'cV[R]_n) :=
  '[e.1, x] == e.2.
Definition sat_eq0 (e : lrel[R]_n) (x : 'cV[R]_n) :=
  '[e.1, x] == 0.

Definition sat_Po (x : 'cV[R]_n) :=
  all (fun e => sat_ineq e x) Po.
Definition mask_eq (m : bitseq) (x : 'cV[R]_n):=
  all (fun e => sat_eq e x) (mask m Po).
Definition nth_eq0 (m : nat) (x : 'cV[R]_n) :=
  sat_eq0 (nth (@be0 R n) Po m) x.
Definition mask_eq0 (m: bitseq) (x : 'cV[R]_n):=
  all (fun e => sat_eq0 e x) (mask m Po).

Definition vertex := (bitseq * 'cV[R]_n)%type.
Definition edge := (bitseq * 'cV[R]_n * bitseq * bitseq)%type.

Definition vertex_mask (v : vertex) := v.1.
Definition vertex_point (v : vertex) := v.2.
Definition edge_mask (e : edge) := e.1.1.1.
Definition edge_norm (e : edge) := e.1.1.2.
Definition edge_fst (e : edge) := e.1.2.
Definition edge_snd (e : edge) := e.2.
Definition edge_maskfst (e : edge) :=
  set_nth false (edge_mask e) (edge_fst e) true.
Definition edge_masksnd (e : edge) :=
  set_nth false (edge_mask e) (edge_snd e) true.

(* TODO : pour tout sommet,
chaque arête incidente est dans la liste des arêtes; et pour chacune de ces arêtes incidentes, on vérifie que le sommet est bien l'un des deux sommets associés à l'arête.
Et chaque arête aura été visitée deux fois exactement durant le processus*)

Definition bipartite (V : seq vertex) (E : seq edge) :=
  let neighbours := tally ((map edge_maskfst E) ++ (map edge_masksnd E)) in
  perm_eq (map fst V) (map fst neighbours) &&
  (all (fun nei => nei.2 == n) neighbours).

Fixpoint vtx_consistent (V : seq vertex) :=
  if V is h::t then
   let: (m,p) := h in
    [&& sat_Po p, mask_eq m p & vtx_consistent t]
  else true.

Fixpoint edge_consistent (E : seq edge) :=
  if E is h::t then
    let: (m,d,m1,m2) := h in
    [&& mask_eq0 m d, ~~ nth_eq0 m1 d, ~~nth_eq0 m2 d & edge_consistent t]
  else true.

Definition algorithm (V : seq vertex) (E : seq edge) :=
  [&& bipartite V E, vtx_consistent V & edge_consistent E].


End Algorithm.

Section TestCarre.

Context (R := rat).

Definition seq_to_lrel (a : seq R) (b : R):=
  BaseElt (pair (\col_(i < size a) (nth 0 a i)) b).
Definition seq_to_cv (a : seq R) :=
  \col_(i < size a) (nth 0 a i).

Definition e1 := seq_to_lrel [:: -1; 0] 0.
Definition e2 := seq_to_lrel [:: 1; 0] 1.
Definition e3 := seq_to_lrel [:: 0; -1] 0.
Definition e4 := seq_to_lrel [:: 0; 1] 1.

Definition Po := [:: e1; e2; e3; e4].
Definition ma1 := [:: true; false; false; false].
Definition ma2 := [:: false; true; false; false].
Definition ma3 := [:: false; false; true; false].
Definition ma4 := [:: false; false; false; true].

Definition d1 := seq_to_cv [:: 1; 0].
Definition d2 := seq_to_cv [:: -1; 0].
Definition d3 := seq_to_cv [:: 0; 1].
Definition d4 := seq_to_cv [:: 0; -1].

Definition edges : seq edge :=
  [::
    (ma1, d1, 2%nat, 3%nat);
    (ma2, d2, 2%nat, 3%nat);
    (ma3, d3, 0%nat, 1%nat);
    (ma4, d4, 0%nat, 1%nat)
  ].

Definition v1 : vertex :=
  ([:: true; false; true; false], seq_to_cv [:: 0; 0]).
Definition v2 : vertex :=
  ([:: true; false; false; true], seq_to_cv [:: 0; 1]).
Definition v3 : vertex :=
  ([:: false; true; false; true], seq_to_cv [:: 1; 1]).
Definition v4 : vertex :=
  ([:: false; true; true; false], seq_to_cv [:: 1; 0]).

Definition vertices := [:: v1; v2; v3; v4].

Eval vm_compute in algorithm Po vertices edges.

End TestCarre.