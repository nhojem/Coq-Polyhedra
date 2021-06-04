(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect finmap.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope fset.

(* -------------------------------------------------------------------- *)
Section FsFun.
Context (K : choiceType) (V : eqType) (d : K -> V).

Fact fsfun_udp_key : unit. Proof. exact: tt. Qed.

Definition fsfun_upd (f : fsfun d) (k : K) (v : V) : fsfun d :=
  [fsfun[fsfun_udp_key]
     x in k |` finsupp f => if x == k then v else f x].

Definition fsfun_dupd (f : fsfun d) (k : K) (v : V) : fsfun d :=
  if k \in finsupp f then f else fsfun_upd f k v.
End FsFun.

Notation "f .[ k <- v ]" := (fsfun_upd f k v) : fun_scope.
Notation "f .[ k <-? v ]" := (fsfun_dupd f k v)
  (at level 2, format "f .[ k  <-?  v ]") : fun_scope.

(* -------------------------------------------------------------------- *)
Section GraphDef.
Context (T : choiceType).

Variant graph :=
  Graph of {fsfun T -> option {fset T} with None}.

Coercion graph_val (G : graph) := let: Graph g := G in g.

Canonical graph_subType := Eval hnf in [newType for graph_val].

Definition graph_eqMixin :=
  Eval hnf in [eqMixin of graph by <:].
Canonical graph_eqType :=
  Eval hnf in EqType graph graph_eqMixin.
Definition graph_choiceMixin :=
  [choiceMixin of graph by <:].
Canonical graph_choiceType :=
  Eval hnf in ChoiceType graph graph_choiceMixin.

Definition graph_of of phant T := graph.
Identity Coercion type_graph_of : graph_of >-> graph.
End GraphDef.

(* -------------------------------------------------------------------- *)
Notation "{ 'graph' T }" := (graph_of (Phant T)) (at level 0).

Section GraphOf.
Context (T : choiceType).

Canonical graph_of_subType    := Eval hnf in [subType    of {graph T}].
Canonical graph_of_eqType     := Eval hnf in [eqType     of {graph T}].
Canonical graph_of_choiceType := Eval hnf in [choiceType of {graph T}].
End GraphOf.

(* -------------------------------------------------------------------- *)
Section GraphBasics.
Context (T : choiceType).

Definition graph0 : graph T :=
  Graph [fsfun].

Definition add_vertex (g : graph T) (v : T) :=
  Graph g.[v <-? Some fset0].

Definition add_edge (g : graph T) (v1 v2 : T) :=
  Graph g.[v1 <- Some (v2 |` odflt fset0 (g v1))].

Definition successors (g : graph T) (v : T) : {fset T} :=
  odflt fset0 (g v).

Definition vertices (g : graph T) : {fset T} :=
  finsupp g.

Definition edges (g : graph T) : rel T :=
  [rel x y | y \in successors g x].

Definition predecessors (g : graph T) (v : T) : {fset T} :=
  [fset x in vertices g | edges g x v].

(* Introduce notation *)
(* create_graph -> mk_graph *)
Definition mk_graph (V : {fset T}) (E : rel T) : graph T :=
  Graph [fsfun v in V => Some [fset w | w in V & E v w] | None].

Section Lemmas.

Lemma in_succE (G : graph T) (x y : T):
  y \in successors G x = edges G x y.
Proof. by []. Qed.

Lemma sub_succ (G : graph T) (x : T):
  x \in vertices G -> successors G x `<=` vertices G.
Proof.
Admitted.

Section MkGraph.
Context (V : {fset T}) (E : rel T).

Lemma vtx_mk_graph : vertices (mk_graph V E) = V.
Proof.
apply/eqP; rewrite eqEfsubset; apply/andP; split.
- exact: finsupp_sub.
- by apply/fsubsetP=> x; rewrite mem_finsupp fsfunE => ->.
Qed.

Lemma edge_mk_graph : edges (mk_graph V E) =2 E.
Proof.
Admitted.
End MkGraph.
End Lemmas.

End GraphBasics.
Section Connected.
Context (T : choiceType) (G : graph T).

(*TODO Paramètres src dst plutôt qu'entrées du Record ?*)
Record gpath := GPath {
  src : T;
  dst : T;
  s : seq T;
  _ : path (edges G) src s;
  _ : last src s = dst
}.

Record epath := EPath {
  p :> gpath;
  _ : uniq (src p :: s p)
}.

Program Definition nil_path (x : T) : epath := @EPath (@GPath x x [::] _ _) _.

Definition is_path (p : epath) (x y : T) := src p = x /\ dst p = y.

Definition has_path (x y : T) := exists p : epath, is_path p x y.

Definition is_npath (n : nat) (p : epath) (x y : T) :=
  is_path p x y /\ size (s p) = n.

Definition has_npath (n : nat) (x y : T) := exists p : epath, is_npath n p x y.

Definition connected := forall x y : T, x \in vertices G -> y \in vertices G ->
  has_path x y.

Lemma has_npath0 (x : T) : has_npath 0 x x.
Proof. by exists (nil_path x); split; split. Qed.

Lemma has_npathS (n : nat) (x y : T):
  has_npath (S n) x y <-> exists2 z, z \in successors G x & has_npath n z y.
Proof.
Admitted.

Lemma has_pathP (x y : T): has_path x y <-> exists n, has_npath n x y.
Proof.
split.
- by case=> p ?; exists (size (s p)); exists p; split.
- by case=> ? [p []]; exists p.
Qed.

(* Inductive reachable : nat -> T -> T -> Prop :=
  |R0 x : reachable 0 x x
  |RS (x y z : T) (n : nat) of edges G x z & reachable n z y : reachable (S n) x y.   *)

End Connected.

Section Regular.
Context (T : choiceType) (G : graph T) (n : nat).

Definition regular := forall v : T, v \in vertices G -> #|` successors G v| = n.

End Regular.

Section GIsomorphism.

Context {T1 T2 : choiceType} (G1 : graph T1) (G2 : graph T2).
Let V1 := vertices G1.
Let V2 := vertices G2.

Definition gbij (f : T1 -> T2) := {in V1&, injective f} /\ (f @` V1 = V2).
Notation gmorph := (fun f : T1 -> T2 => 
  {in V1&, forall x y, edges G1 x y = edges G2 (f x) (f y)}).
Definition gisof f := gbij f /\ gmorph f. 
Definition giso := exists f, gisof f.

End GIsomorphism.

Section IsoProofs.

Context {T1 T2 : choiceType}.

Lemma iso_mk_grph (V1 : {fset T1}) (V2 : {fset T2}) (E1 : rel T1) (E2 : rel T2):
  giso (mk_graph V1 E1) (mk_graph V2 E2) <->
  exists (f: T1 -> T2),
  [/\ {in V1&, injective f}, (f @` V1 = V2) &
    {in V1&, forall x y, E1 x y = E2 (f x) (f y)}].
Proof.
split.
- case=> f [[]]; rewrite !vtx_mk_graph=> ?? morph; exists f; split=> //.
  by move=> x y xV1 yV1; move: (morph x y xV1 yV1); rewrite !edge_mk_graph.
- case=> f [?? morph]; exists f; first split; first split; rewrite !vtx_mk_graph //.
  move=> ????; rewrite ?edge_mk_graph; exact: morph.
Qed.

Section Foo.
Context (G1 : graph T1) (G2 : graph T2) (f : T1 -> T2) (n : nat).
Let V1 := vertices G1.
Let V2 := vertices G2.
Let E1 := edges G1.
Let E2 := edges G2.
Hypothesis f_inj: {in V1&, injective f}.
Hypothesis f_leq: (f @` V1) `<=` V2.
Hypothesis f_morph : {in V1&, forall x y, E1 x y -> E2 (f x) (f y)}.
Hypothesis G2_connected : connected G2.
Hypothesis G1_regular : regular G1 n.
Hypothesis G2_regular : regular G2 n.

Lemma foo_succE:
  {in V1, forall x, f @` (successors G1 x) = (successors G2 (f x))}.
Proof.
move=> x xV1; apply/eqP; rewrite eqEfcard; apply/andP; split.
- apply/fsubsetP=> y /imfsetP [y' /= y'succ ->].
  move/fsubsetP: (sub_succ xV1) => /(_ y' y'succ) y'V1.
  rewrite in_succE; exact: f_morph.
- move/fsubsetP: f_leq => imf.
  rewrite card_in_imfset ?G1_regular ?G2_regular ?imf ?in_imfset //=.
  move/fsubsetP: (sub_succ xV1) => succ1 p q /succ1 pV1 /succ1 qV1; exact: f_inj.
Qed.

Lemma bar : gisof G1 G2 f.
Proof.
Admitted.
End Foo.

End IsoProofs.
