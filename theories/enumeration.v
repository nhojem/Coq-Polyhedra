Require Import Recdef.
From mathcomp Require Import all_ssreflect all_algebra finmap.
(* Require Import extra_misc inner_product extra_matrix xorder vector_order row_submx vector_order.
Require Import hpolyhedron polyhedron barycenter poly_base. *)
Require Import BinNums FMapAVL OrderedTypeEx.
From Bignums Require Import BigQ.

Import Order.Theory.
(* Import GRing.Theory Num.Theory. *)

(* Local Open Scope ring_scope. *)
(* Local Open Scope poly_scope. *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Definition foo (L1 L2 : seq nat) := match L1, L2 with
  |[::], _ => Some true
  |_ , [::] => Some false
  |_, _ => None
end.

Parameter L: seq nat.
Check erefl: foo [::] L = Some true.
Fail Check erefl: foo L [::] = Some false.
  *)

Module Bitseq_as_UOT <: UsualOrderedType.
Definition t := bitseq.
Definition eq := @eq bitseq.
Definition eq_refl := @Coq.Init.Logic.eq_refl t.
Definition eq_sym := @Coq.Init.Logic.eq_sym t.
Definition eq_trans := @Coq.Init.Logic.eq_trans t.
Fixpoint bitseq_cmp (x y : bitseq) : comparison :=
  match x, y with
  |[::], [::] => Eq
  |[::], _ => Lt
  |_, [::] => Gt
  |true::_, false::_ => Gt
  |false::_, true::_ => Lt
  |_::tx, _::ty => bitseq_cmp tx ty
  end.

Definition bitseq_lt (x y: bitseq) : Prop := (bitseq_cmp x y) = Lt.

Definition lt:= bitseq_lt.

Lemma lt_trans : forall x y z, lt x y -> lt y z -> lt x z.
Proof.
move=> + y; elim: y => /=.
- by case => //=; case.
- case => /= ty IH [|[] tx] [|[] tz] //=; exact: IH.
Qed.

Lemma lt_not_eq x : forall y, lt x y -> ~ eq x y.
Proof.
elim: x => [|hx tx IH] [|hy ty] //=.
by case: hx; case: hy => // /IH /eqP txnty; apply/eqP; rewrite eqseq_cons. 
Qed.


Program Definition compare x y : OrderedType.Compare lt eq x y :=
  match (bitseq_cmp x y) with
  |Lt => OrderedType.LT _
  |Eq => OrderedType.EQ _
  |Gt => OrderedType.GT _
  end.


Next Obligation. by []. Qed.
Next Obligation.
move: y Heq_anonymous; elim: x => [|hx tx IH]. 
- by case.
- by case => [|hy ty]; case: hx => //; case: hy => //= /IH ?; congr (_ :: _).
Qed.
Next Obligation.
move: y Heq_anonymous; elim x => [|hx tx IH].
- by case.
- by case => // hy ty; case: hx; case: hy => //= /IH;
  rewrite /lt /bitseq_lt /=.
Qed.


Lemma eq_dec x y : {(eq x y)} + {(~ eq x y)}.
Proof. rewrite /eq; exact: (Bool.reflect_dec _ _ (@eqP _ x y)). Qed.

End Bitseq_as_UOT.
Module BM := Make(Bitseq_as_UOT).

(* --------------------------------------------------------------------------------------------------- *)

Module Type Prerequisite.
Parameters (U L : Type).
(* L is the type of linear equations, U is a vector space*)
Parameters sat_ineq sat_eq sat_eq0: L -> U -> bool.
End Prerequisite.

Module Algorithm (P : Prerequisite).
Import P.

Definition sat_Po Po (x : U) :=
  all (fun e => sat_ineq e x) Po.
Definition mask_eq Po (m : bitseq) (x : U):=
  all (fun e => sat_eq e x) (mask m Po).
Definition mask_eq0 Po (m: bitseq) (x : U):=
  all (fun e => sat_eq0 e x) (mask m Po).

Definition vertex := (bitseq * U)%type.
Record edge_d := Edge {norm : U; m1 : bitseq; m2 :bitseq}.

Definition vtx_mask (v : vertex) := v.1.
Definition vtx_point (v : vertex) := v.2.

Definition mask_incident (s:bitseq) :=
  let fix aux temp cur res :=
    if cur is h::t then
      if h is true then
        aux (rcons temp h) t (((rcons temp false) ++ t)::res)
        else aux (rcons temp h) t res
    else res
  in aux [::] s [::].
(*mask_incident s returns every mask equal to s except one true changed to false*)

Fixpoint mask_cardinal (s:bitseq) :=
  if s is h::t then
    if h is true then (S (mask_cardinal t)) else mask_cardinal t
  else 0%nat.
(*Count the number of true in a bitseq*)

Fixpoint eq_bitseq (p q : bitseq) :=
  match p, q with
  |hp::tp, hq::tq => (hp == hq) && eq_bitseq tp tq
  |[::], [::] => true
  |_, _ => false
  end.

Definition obind2 (A B C: Type) (f : A -> B -> option C) x y :=
  if x is Some x then f x y else None.


Definition vtx_explore (E : BM.t edge_d) (res : BM.t (nat * nat)) (v : vertex) :=
  let: (m_v, _) := v in
  let incidents := mask_incident m_v in
  let vtx_explore_aux res m :=
    if BM.find m E is Some (Edge _ m1 m2) then
      let eqm1 := eq_bitseq m_v m1 in
      let eqm2 := eq_bitseq m_v m2 in
      if BM.find m res is Some (n1, n2) then
        Some (BM.add m ((n1 + eqm1), (n2 + eqm2))%N res)
      else Some (BM.add m (nat_of_bool eqm1, nat_of_bool eqm2) res)
    else None
  in foldl (obind2 vtx_explore_aux) (Some res) incidents.


(* map of edges*)

(* For each vertex v and edge list E, vtx_incident_edges v E returns a seq (option bitseq), such that (Some m) means that m is an incident edge of v, m is in E and v is one of the two vertices associated to m*)


Definition bipartite (V : seq vertex) (E : BM.t edge_d) :=
  let map_res0 := BM.map (fun _ => (0, 0)%N) E in
  let map_res := foldl (obind2 (vtx_explore E)) (Some map_res0) V in
  if map_res is Some m then
    BM.fold (fun _ el b => b && (el == (1, 1)%N)) m true
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

Definition vtx_consistent n Po (V : seq vertex) :=
  all (fun v => [&& sat_Po Po (vtx_point v), mask_eq Po (vtx_mask v) (vtx_point v) & mask_cardinal (vtx_mask v) == n]) V.

Fixpoint except_one (p q : bitseq) :=
  match p, q with
  |[::], [::] => false
  |hp::tp, hq::tq => if (hp == hq) then except_one tp tq else eq_bitseq tp tq
  |_, _ => false
  end.

Definition edge_consistent n Po (E : BM.t edge_d) :=
  BM.fold (fun m elt b => 
    [&& b, mask_eq0 Po m (norm elt), ~~ mask_eq0 Po (m1 elt) (norm elt), ~~mask_eq0 Po (m2 elt) (norm elt), (mask_cardinal m == (n-1)%N), except_one m (m1 elt) & except_one m (m2 elt)])
    E true. 


End Algorithm.

(* Section TestCarre.

  Context (R := rat) (L := ((seq R) * R)%type) (U := seq R).

  Definition e1 : L := ([:: -1; 0], 0)%R.
  Definition e2 : L := ([:: 1; 0], 1)%R.
  Definition e3 : L := ([:: 0; -1], 0)%R.
  Definition e4 : L := ([:: 0; 1], 1)%R.

  Definition Po := [:: e1; e2; e3; e4].
  Definition ma1 := [:: true; false; false; false].
  Definition ma2 := [:: false; true; false; false].
  Definition ma3 := [:: false; false; true; false].
  Definition ma4 := [:: false; false; false; true].
  Definition ma13 := [:: true; false; true; false].
  Definition ma14 := [:: true; false; false; true].
  Definition ma23 := [:: false; true; true; false].
  Definition ma24 := [:: false; true; false; true].

  Definition d1 : U := [:: 0; 1]%R.
  Definition d2 : U := [:: 0; -1]%R.
  Definition d3 : U := [:: 1; 0]%R.
  Definition d4 : U := [:: -1; 0]%R.

  Definition edges0 := BM.empty (edge_d U).
  Definition edges1 := BM.add ma1 (Edge d1 ma13 ma14) edges0.
  Definition edges2 := BM.add ma2 (Edge d2 ma23 ma24) edges1.
  Definition edges3 := BM.add ma3 (Edge d3 ma13 ma23) edges2.
  Definition edges := BM.add ma4 (Edge d4 ma14 ma24) edges3.


  Definition v1 : vertex U := (ma13, [:: 0; 0]%R).
  Definition v2 : vertex U := (ma14, [:: 0; 1]%R).
  Definition v3 : vertex U := (ma24, [:: 1; 1]%R).
  Definition v4 : vertex U := (ma23, [:: 1; 0]%R).

  Definition vertices := [:: v1; v2; v3; v4].

  Fixpoint test_dot (x y : U) : R :=
    if (x, y) is (x'::tx, y'::ty) then
      ((x' * y') + test_dot tx ty)%R
    else 0%R. 

  Definition sat_ineq (e: L) (x : U) :=
    ((test_dot e.1 x) <= e.2)%R.

  Definition sat_eq (e: L) (x : U) :=
    ((test_dot e.1 x) == e.2)%R.

  Definition sat_eq0 (e: L) (x : U) :=
    ((test_dot e.1 x) == 0)%R.

  Eval vm_compute in bipartite vertices edges.
  Eval vm_compute in vtx_consistent 2%N Po sat_ineq sat_eq vertices.
  Eval vm_compute in edge_consistent 2%N Po sat_eq0 edges.
  Eval vm_compute in algorithm 2%N Po sat_ineq sat_eq sat_eq0 vertices edges.


End TestCarre. *)

Module BigQPrerequisite <: Prerequisite.
Definition U := seq bigQ.
Definition L := seq bigQ.

(*e : L is a list denoting a linear relation, s.t h::t corresponds to <t,x> >= h *)

Definition bigQ_dot (x y : U) : bigQ :=
  let aux := (fun res p => BigQ.add_norm res (BigQ.mul_norm p.1 p.2)) in
  foldl aux 0%bigQ (zip x y).

Definition sat_ineq (e : L) (x : U) :=
  if e is h::t then
    let r := (bigQ_dot t x) in
    match (r ?= -h)%bigQ with
    |Gt => true
    |Eq => true
    |Lt => true
    end
  else false.

Definition sat_eq (e : L) (x : U) :=
  if e is h::t then
    let r := (bigQ_dot t x) in
    if (r ?= (- h))%bigQ is Eq then true else false
  else false.

Definition sat_eq0 (e : L) (x : U) :=
  if e is h::t then
    let r := (bigQ_dot t x) in
    if (r ?= 0)%bigQ is Eq then true else false
  else false.

End BigQPrerequisite.

Module BigQAlgorithm := Algorithm BigQPrerequisite.


Definition bigQ_vtx_consistent :=
  BigQAlgorithm.vtx_consistent.

Definition bigQ_edge_consistent :=
  BigQAlgorithm.edge_consistent.

Definition bigQ_bipartite := BigQAlgorithm.bipartite.


Section BigQ_misc.


Definition seq_to_map (L : seq (bitseq * (seq bigQ) * bitseq * bitseq)) :=
  foldr
  (fun x m => let: (key, norm, v1, v2) := x in (BM.add key (BigQAlgorithm.Edge norm v1 v2) m))
  (BM.empty (BigQAlgorithm.edge_d)) L.
  


End BigQ_misc.

(* Section TestExtract.

  Local Open Scope bigQ_scope.

  Definition Po: seq (seq bigQ) := [::
    [:: 1; 1; 0; 0]
  ;  [:: 1; 0; 1; 0]
  ;  [:: 1; 0; 0; 1]
  ;  [:: 1; -1; 0; 0]
  ;  [:: 1; 0; 0; -1]
  ;  [:: 1; 0; -1; 0]
  ].

  Definition n : nat := 3.

  Definition v_data_0000 : seq (bitseq * (seq bigQ)) := [::
    ([:: false; false; false; true; true; true], [:: 1; 1; 1])
  ;  ([:: true; false; false; false; true; true], [:: -1; 1; 1])
  ;  ([:: false; false; true; true; false; true], [:: 1; 1; -1])
  ;  ([:: true; false; true; false; false; true], [:: -1; 1; -1])
  ;  ([:: false; true; true; true; false; false], [:: 1; -1; -1])
  ;  ([:: true; true; true; false; false; false], [:: -1; -1; -1])
  ;  ([:: false; true; false; true; true; false], [:: 1; -1; 1])
  ;  ([:: true; true; false; false; true; false], [:: -1; -1; 1])
  ].

  Definition e_data_0000 : seq (bitseq * (seq bigQ) * bitseq * bitseq) := [::
    ([:: false; false; false; false; true; true], [:: 1; 0; 0], [:: false; false; false; true; true; true], [:: true; false; false; false; true; true])
  ; ([:: false; false; false; true; false; true], [:: 0; 0; 1], [:: false; false; false; true; true; true], [:: false; false; true; true; false; true])
  ; ([:: false; false; true; false; false; true], [:: 1; 0; 0], [:: false; false; true; true; false; true], [:: true; false; true; false; false; true])
  ; ([:: true; false; false; false; false; true], [:: 0; 0; 1], [:: true; false; false; false; true; true], [:: true; false; true; false; false; true])
  ; ([:: false; false; true; true; false; false], [:: 0; 1; 0], [:: false; false; true; true; false; true], [:: false; true; true; true; false; false])
  ; ([:: false; true; true; false; false; false], [:: 1; 0; 0], [:: false; true; true; true; false; false], [:: true; true; true; false; false; false])
  ; ([:: true; false; true; false; false; false], [:: 0; 1; 0], [:: true; false; true; false; false; true], [:: true; true; true; false; false; false])
  ; ([:: false; false; false; true; true; false], [:: 0; 1; 0], [:: false; false; false; true; true; true], [:: false; true; false; true; true; false])
  ; ([:: false; true; false; true; false; false], [:: 0; 0; 1], [:: false; true; true; true; false; false], [:: false; true; false; true; true; false])
  ; ([:: false; true; false; false; true; false], [:: 1; 0; 0], [:: false; true; false; true; true; false], [:: true; true; false; false; true; false])
  ; ([:: true; false; false; false; true; false], [:: 0; 1; 0], [:: true; false; false; false; true; true], [:: true; true; false; false; true; false])
  ; ([:: true; true; false; false; false; false], [:: 0; 0; 1], [:: true; true; true; false; false; false], [:: true; true; false; false; true; false])
  ].

  Definition v_list : seq (bitseq * (seq bigQ)) := Eval vm_compute in 
    v_data_0000
  .

  Definition e_list : seq (bitseq * (seq bigQ) * bitseq * bitseq) := Eval vm_compute in
    e_data_0000
  .

  Definition output :=
    Eval native_compute in bigQ_algorithm n Po v_list (seq_to_map e_list).

  Print output.

End TestExtract. *)