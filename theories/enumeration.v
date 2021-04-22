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

(* Definition foo (L1 L2 : seq nat) := match L1, L2 with
  |[::], _ => Some true
  |_ , [::] => Some false
  |_, _ => None
end.

Parameter L: seq nat.
Check erefl: foo [::] L = Some true.
Fail Check erefl: foo L [::] = Some false.
  *)

(* Module Bitseq_as_UOT <: UsualOrderedType.
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
Module BM := FMapAVL.Make(Bitseq_as_UOT).
Module BF := FSetAVL.Make(Bitseq_as_UOT). *)

(* --------------------------------------------------------------------------------------------------- *)

Module Type Prerequisite.
Parameters (U L : Type).
(* L is the type of linear equations, U is a vector space*)
Parameters sat_ineq sat_eq: L -> U -> bool.
(* Parameter extract_matrix : seq L -> (seq R).
(*inverses A B checks if B = transpose of A^-1*)
Parameter inverses : seq U -> seq U -> bool. *)

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
(* Definition is_inv (m : bitseq) M :=
  inverses (mask m A) M. *)

(* Definition mask_eq0 (m: bitseq) (x : U) :=
  all (fun e => sat_eq0 e x) (mask m Po). *)

(* Definition vertex := (bitseq * U)%type.
Record edge_d := Edge {norm : U; m1 : bitseq; m2 :bitseq}.

Definition vtx_mask (v : vertex) := v.1.
Definition vtx_point (v : vertex) := v.2. *)

Definition vertex_consistent :=
  let f := fun masq v b =>
    if b is false then false else
    let: (x, _) := v in
    mask_eq masq x && sat_Po x
  in AlgoGraph.vertex_fold f G true.

Fixpoint inter_card (p q : bitseq) :=
  match p,q with
  |[::], [::] => 0%nat
  |_, [::] => 0%nat
  |[::], _ => 0%nat
  |true::p', true::q' => (1 + inter_card p' q')%nat
  |_::p', _::q' => inter_card p' q'
  end.

Definition neighbour_condition I :=
  (AlgoGraph.neighbour_all
    (fun J => inter_card I J == (n-1)%nat) G I) &&
  (AlgoGraph.nb_neighbours I G == Some n).

Definition struct_consistent :=
  AlgoGraph.vertex_all (fun I _ => neighbour_condition I) G.



End Body.
End Algorithm.

Module BigQPrerequisite <: Prerequisite.

Definition U := seq (seq bigQ).
Definition L := (seq bigQ * seq bigQ)%type.

(*e : L as form (b, a), with size b = 1 + m, representing the inequation a * x <=_lex b*)

Definition bigQ_dot (x y : seq bigQ) : bigQ :=
  let aux := (fun res p => BigQ.add_norm res (BigQ.mul_norm p.1 p.2)) in
  foldl aux 0%bigQ (zip x y).

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
  let: (b, a) := c in
  let ax := map (fun l => bigQ_dot a l) x in
  lex_order ax b.

Fixpoint eq_seq_bigQ (x y : seq bigQ) :=
  match x, y with
  |[::], [::] => true
  |hx::tx, hy::ty =>
    if (hx ?= hy)%bigQ is Eq then eq_seq_bigQ tx ty else false 
  |_, _ => false
  end.
  

Definition sat_eq (c : L) (x : U) :=
  let: (b, a) := c in
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

  Definition Po: seq (seq bigQ * seq bigQ) := [::
    ([:: 1; 1; 0; 0; 0; 0; 0], [::-1; 0; 0])
  ;  ([:: 1; 0; 1; 0; 0; 0; 0], [::0; -1; 0])
  ;  ([:: 1; 0; 0; 1; 0; 0; 0], [::0; 0; -1])
  ;  ([:: 1; 0; 0; 0; 1; 0; 0], [::1; 0; 0])
  ;  ([:: 1; 0; 0; 0; 0; 1; 0], [::0; 0; 1])
  ;  ([:: 1; 0; 0; 0; 0; 0; 1], [::0; 1; 0])
  ].

  Definition m : nat := 6%N.
  Definition n : nat := 3%N.

  Definition v_list : seq (bitseq * (seq (seq bigQ))) := Eval vm_compute in 
    v_data_0000
  .

  Definition e_list : seq (bitseq * bitseq) := Eval vm_compute in
    e_data_0000
  .

  Definition input :=
      BigQAlgorithm.AlgoGraph.add_edges e_list (BigQAlgorithm.AlgoGraph.add_vertices v_list BigQAlgorithm.AlgoGraph.empty).

  Definition vtx_output :=
    Eval native_compute in bigQ_vtx_consistent Po input.

  Definition struct_output :=
      Eval native_compute in bigQ_struct_consistent n input.

  Print vtx_output.
  Print struct_output.

End TestExtract. *)

