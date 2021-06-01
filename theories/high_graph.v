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

Notation "f .[ k <-? v ]" := (fsfun_upd f k v)
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
Definition create_graph (V : {fset T}) (E : rel T) : graph T :=
  Graph [fsfun v in V => Some [fset w | w in V & E v w] | None].

Section Lemmas.
Context (V : {fset T}) (E : rel T).

Lemma vtx_create_graph : vertices (create_graph V E) = V.
Proof.
apply/eqP; rewrite eqEfsubset; apply/andP; split.
- exact: finsupp_sub.
- by apply/fsubsetP=> x; rewrite mem_finsupp fsfunE => ->.
Qed.

End Lemmas.

End GraphBasics.



Section Connected.
Context (T : choiceType) (G : graph T).

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

Definition connected := forall x y : T, x \in vertices G -> y \in vertices G ->
  exists2 p : epath, src p = x & dst p = y.

End Connected.

Section Regular.
Context (T : choiceType) (G : graph T) (n : nat).

Definition regular := forall v : T, v \in vertices G -> #|` successors G v| = n.

End Regular.
