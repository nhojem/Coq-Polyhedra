Require Import Recdef.
From mathcomp Require Import all_ssreflect all_algebra finmap.
(* Require Import extra_misc inner_product extra_matrix xorder vector_order row_submx vector_order.
Require Import hpolyhedron polyhedron barycenter poly_base. *)
Require BinNums FSetAVL.
From Bignums Require Import BigQ.
Require Import graph MapFold.

Import Order.Theory.
(* Import GRing.Theory Num.Theory. *)

(* Local Open Scope ring_scope. *)
(* Local Open Scope poly_scope. *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Misc.

Definition card_bitseq (p : bitseq) :=
  count id p.

Fixpoint inter_card (p q : bitseq) :=
  match p,q with
  |[::], [::] => 0%nat
  |_, [::] => 0%nat
  |[::], _ => 0%nat
  |true::p', true::q' => (1 + inter_card p' q')%nat
  |_::p', _::q' => inter_card p' q'
  end.

End Misc.

(* --------------------------------------------------------------------------------------------------- *)

Module Type Prerequisite.
Parameters (U L : Type).
(* L is the type of linear equations, U is a vector space*)
Parameters sat_ineq sat_eq: L -> U -> bool.

End Prerequisite.



Module Algorithm (P : Prerequisite).
Import P.

Module Vertex <: Label.
Definition t := U.
End Vertex.

Module O <: Sig.
Fact d : unit. Proof. exact: tt. Qed.
Definition T := [orderType of (seqlexi_with d bool)].
End O.

Module AlgoGraph := Graph O Vertex.


Section Body.
Context (n : nat) (Po : seq L) (G : AlgoGraph.t).
(* Definition A := extract_matrix Po. *)


Definition sat_Po (x : U) :=
  all (fun e => sat_ineq e x) Po.
Definition mask_eq (m : bitseq) (x : U):=
  all (fun e => sat_eq e x) (mask m Po).


Definition vertex_consistent :=
  let f masq x := mask_eq masq x.1 && sat_Po x.1
  in AlgoGraph.vertex_all f G.

Definition neighbour_condition I :=
  [&& (size I == size Po),
  card_bitseq I == n,
  (AlgoGraph.neighbour_all
    (fun J => inter_card I J == (n-1)%nat) G I) &
  (AlgoGraph.nb_neighbours I G == Some n)].

Definition struct_consistent :=
  AlgoGraph.vertex_all (fun I _ => neighbour_condition I) G.



End Body.
End Algorithm.

Module BigQPrerequisite <: Prerequisite.

Definition U := seq (seq bigQ).
Definition L := (seq bigQ * seq bigQ)%type.

(*e : L as form (a, b), with size b = 1 + m, representing the inequation a * x <=_lex b*)

Definition bigQ_dot (x y : seq bigQ) : bigQ :=
  let aux := (fun p res => BigQ.add_norm res (BigQ.mul_norm p.1 p.2)) in
  foldr aux 0%bigQ (zip x y).
(* QC: changed foldl into foldr. Mandatory ?*)

Fixpoint lex_order (x y : seq bigQ) :=
  match x, y with
  |[::], [::] => true
  |hx::tx, hy::ty => match (hx ?= hy)%bigQ with
    |Lt => true
    |Gt => false
    |Eq => lex_order tx ty
    end
  |_, _ => false
  end.

Definition sat_ineq (c : L) (x : U) :=
  let: (a, b) := c in
  let ax := map (fun l => bigQ_dot a l) x in
  lex_order b ax.

Fixpoint eq_seq_bigQ (x y : seq bigQ) :=
  match x, y with
    |[::], [::] => true
    |a::l, b::l' => BigQ.eqb a b && eq_seq_bigQ l l'
    |_, _ => false
  end.
  

Definition sat_eq (c : L) (x : U) :=
  let: (a, b) := c in
  let ax := map (fun l => bigQ_dot a l) x in
  eq_seq_bigQ ax b.


End BigQPrerequisite.

Module BigQAlgorithm := Algorithm BigQPrerequisite.


Definition bigQ_vtx_consistent :=
  BigQAlgorithm.vertex_consistent.

Definition bigQ_struct_consistent :=
  BigQAlgorithm.struct_consistent.

(* Section TestExtract.

Local Open Scope bigQ_scope.

Definition Po: seq (seq bigQ * seq bigQ) := [::
   ([:: -1; 0; 0], [::1; 1; 0; 0; 0; 0; 0])
;  ([:: 0; -1; 0], [::1; 0; 1; 0; 0; 0; 0])
;  ([:: 0; 0; -1], [::1; 0; 0; 1; 0; 0; 0])
;  ([:: 1; 0; 0], [::1; 0; 0; 0; 1; 0; 0])
;  ([:: 0; 0; 1], [::1; 0; 0; 0; 0; 1; 0])
;  ([:: 0; 1; 0], [::1; 0; 0; 0; 0; 0; 1])
].

Definition m : nat := 6%N.
Definition n : nat := 3%N.

Definition v_data_0000 : seq (bitseq * (seq (seq bigQ))) := [::
   ([:: false; false; false; true; true; true], [:: 
  [:: 1; 1; 1 ]
; [:: 0; 0; 0 ]
; [:: 0; 0; 0 ]
; [:: 0; 0; 0 ]
; [:: 1; 0; 0 ]
; [:: 0; 0; 1 ]
; [:: 0; 1; 0 ]
])
;  ([:: true; false; false; false; true; true], [:: 
  [:: -1; 1; 1 ]
; [:: -1; 0; 0 ]
; [:: 0; 0; 0 ]
; [:: 0; 0; 0 ]
; [:: 0; 0; 0 ]
; [:: 0; 0; 1 ]
; [:: 0; 1; 0 ]
])
;  ([:: false; false; true; true; false; true], [:: 
  [:: 1; 1; -1 ]
; [:: 0; 0; 0 ]
; [:: 0; 0; 0 ]
; [:: 0; 0; -1 ]
; [:: 1; 0; 0 ]
; [:: 0; 0; 0 ]
; [:: 0; 1; 0 ]
])
;  ([:: true; false; true; false; false; true], [:: 
  [:: -1; 1; -1 ]
; [:: -1; 0; 0 ]
; [:: 0; 0; 0 ]
; [:: 0; 0; -1 ]
; [:: 0; 0; 0 ]
; [:: 0; 0; 0 ]
; [:: 0; 1; 0 ]
])
;  ([:: false; true; true; true; false; false], [:: 
  [:: 1; -1; -1 ]
; [:: 0; 0; 0 ]
; [:: 0; -1; 0 ]
; [:: 0; 0; -1 ]
; [:: 1; 0; 0 ]
; [:: 0; 0; 0 ]
; [:: 0; 0; 0 ]
])
;  ([:: true; true; true; false; false; false], [:: 
  [:: -1; -1; -1 ]
; [:: -1; 0; 0 ]
; [:: 0; -1; 0 ]
; [:: 0; 0; -1 ]
; [:: 0; 0; 0 ]
; [:: 0; 0; 0 ]
; [:: 0; 0; 0 ]
])
;  ([:: false; true; false; true; true; false], [:: 
  [:: 1; -1; 1 ]
; [:: 0; 0; 0 ]
; [:: 0; -1; 0 ]
; [:: 0; 0; 0 ]
; [:: 1; 0; 0 ]
; [:: 0; 0; 1 ]
; [:: 0; 0; 0 ]
])
;  ([:: true; true; false; false; true; false], [:: 
  [:: -1; -1; 1 ]
; [:: -1; 0; 0 ]
; [:: 0; -1; 0 ]
; [:: 0; 0; 0 ]
; [:: 0; 0; 0 ]
; [:: 0; 0; 1 ]
; [:: 0; 0; 0 ]
])
].

Definition e_data_0000 : seq (bitseq * bitseq) := [::
  ([:: true; false; false; false; true; true], [:: false; false; false; true; true; true])
; ([:: false; false; true; true; false; true], [:: false; false; false; true; true; true])
; ([:: true; false; true; false; false; true], [:: false; false; true; true; false; true])
; ([:: true; false; true; false; false; true], [:: true; false; false; false; true; true])
; ([:: false; true; true; true; false; false], [:: false; false; true; true; false; true])
; ([:: true; true; true; false; false; false], [:: false; true; true; true; false; false])
; ([:: true; true; true; false; false; false], [:: true; false; true; false; false; true])
; ([:: false; true; false; true; true; false], [:: false; false; false; true; true; true])
; ([:: false; true; false; true; true; false], [:: false; true; true; true; false; false])
; ([:: true; true; false; false; true; false], [:: false; true; false; true; true; false])
; ([:: true; true; false; false; true; false], [:: true; false; false; false; true; true])
; ([:: true; true; false; false; true; false], [:: true; true; true; false; false; false])
].

Definition G := Eval native_compute in BigQAlgorithm.AlgoGraph.empty.


Definition G_0 :=  Eval native_compute in BigQAlgorithm.AlgoGraph.add_vertices v_data_0000 G.
Definition H_0 := BigQAlgorithm.AlgoGraph.add_edges e_data_0000 G_0.
Definition input := Eval native_compute in H_0.

Definition vtx_output :=
  Eval native_compute in bigQ_vtx_consistent Po input.

Definition struct_output :=
    Eval native_compute in bigQ_struct_consistent n input.

Print vtx_output.
Print struct_output.

End TestExtract. *)