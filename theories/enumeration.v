Require Import Recdef.
From mathcomp Require Import all_ssreflect all_algebra finmap.
Require Import extra_misc inner_product extra_matrix xorder vector_order row_submx vector_order.
Require Import hpolyhedron polyhedron barycenter poly_base.

Require Import BinNums FMapAVL OrderedTypeEx.

Import Order.Theory.
(* Import GRing.Theory Num.Theory. *)

(* Local Open Scope ring_scope. *)
Local Open Scope poly_scope.

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

Print Module Type UsualOrderedType.
Module Bitseq_as_UOT <: UsualOrderedType.
Definition t := bitseq.
Definition eq := @eq bitseq.
Definition eq_refl := @Coq.Init.Logic.eq_refl t.
Definition eq_sym := @Coq.Init.Logic.eq_sym t.
Definition eq_trans := @Coq.Init.Logic.eq_trans t.
Fixpoint bitseq_lt (x y : bitseq) : Prop := match x, y with
  |_, [::] => False
  |[::], _ => True
  |true::_, false::_ => False
  |false::_, true::_ => True
  |_::tx, _::ty => bitseq_lt tx ty
end.

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

Print OrderedType.Compare.
Fixpoint compare x y : OrderedType.Compare lt eq x y.
Proof.
case: x; case: y.
- exact:OrderedType.EQ.
- move=> ??; exact:OrderedType.LT.
- move=> ??; exact:OrderedType.GT.
- case => y'; case => x'.
  + case: (compare x' y') => ?.
    - exact:OrderedType.LT.
    - by apply:OrderedType.EQ; rewrite/eq; congr (_ :: _).
    - exact:OrderedType.GT.
  + exact:OrderedType.LT.
  + exact:OrderedType.GT.
  + case: (compare x' y') => ?.
    - exact:OrderedType.LT.
    - by apply:OrderedType.EQ; rewrite/eq; congr (_ :: _).
    - exact:OrderedType.GT.
Defined.

Lemma eq_dec x y : {(eq x y)} + {(~ eq x y)}.
Proof. rewrite /eq; exact: (Bool.reflect_dec _ _ (@eqP _ x y)). Qed.

End Bitseq_as_UOT.
Module BM := Make(Bitseq_as_UOT).



(* Section Misc.
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

Fixpoint map_of_bitseq_aux (s : seq bitseq) (m : PositiveMap.t nat) :=
  if s is h::t then
    let x := (b_to_p h) in
    if PositiveMap.find x m is Some n then
      map_of_bitseq_aux t (PositiveMap.add x (S n)%nat m)
    else map_of_bitseq_aux t (PositiveMap.add x (1%nat) m)
  else m.

Definition map_of_bitseq (s : seq bitseq) :=
  map_of_bitseq_aux s (PositiveMap.empty nat).

End Misc. *)

Section Algorithm.
Context (n:nat) (L U: Type) (dft : L).
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
Record edge_d := Edge {norm : U; m1 : bitseq; m2 :bitseq}.

Definition vtx_mask (v : vertex) := v.1.
Definition vtx_point (v : vertex) := v.2.
(* Definition edge_mask (e : edge) := e.1.1.1.
Definition edge_norm (e : edge) := e.1.1.2.
Definition edge_fst (e : edge) := e.1.2.
Definition edge_snd (e : edge) := e.2. *)

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

Compute (0 + eq_bitseq [:: true; false] [:: true; false])%N.

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
    BM.fold (fun ke el b => b && (el == (1, 1)%N)) m true
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

Definition vtx_consistent (V : seq vertex) :=
  all (fun v => [&& sat_Po (vtx_point v), mask_eq (vtx_mask v) (vtx_point v) & mask_cardinal (vtx_mask v) == n]) V.

Fixpoint except_one (p q : bitseq) :=
  match p, q with
  |[::], [::] => false
  |hp::tp, hq::tq => if (hp == hq) then except_one tp tq else eq_bitseq tp tq
  |_, _ => false
  end.

Definition edge_consistent (E : BM.t edge_d) :=
  BM.fold (fun m elt b => 
    [&& b, mask_eq0 m (norm elt), ~~ mask_eq0 (m1 elt) (norm elt), ~~mask_eq0 (m2 elt) (norm elt), (mask_cardinal m == (n-1)%N), except_one m (m1 elt) & except_one m (m2 elt)])
    E true. 

Definition algorithm (V : seq vertex) (E : BM.t edge_d) :=
  [&& bipartite V E, vtx_consistent V & edge_consistent E].


End Algorithm.

Section TestCarre.

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


End TestCarre.