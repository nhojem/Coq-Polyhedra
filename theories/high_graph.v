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
  walk : seq T;
  _ : src \in vertices G;
  _ : path (edges G) src walk;
  _ : last src walk = dst
}.

Record epath := EPath {
  p :> gpath;
  _ : uniq (src p :: walk p)
}.

Definition is_path (p : epath) (x y : T) := src p = x /\ dst p = y.
Definition has_path (x y : T) := exists p : epath, is_path p x y.
Definition size_path (p : epath) := size (walk p).
Definition is_npath (n : nat) (p : epath) (x y : T) :=
  is_path p x y /\ size_path p = n.
Definition has_npath (n : nat) (x y : T) := exists p : epath, is_npath n p x y.
Definition connected := forall x y : T, has_path x y.

Lemma mem_src (p : epath) : src p \in vertices G. Proof. by case: p => -[]. Qed.
Lemma path_walk (p : epath) : path (edges G) (src p) (walk p). Proof. by case: p => -[]. Qed.
Lemma last_dst (p : epath) : last (src p) (walk p) = (dst p). Proof. by case: p => -[]. Qed.
Lemma uniq_walk (p : epath) : uniq (src p :: walk p). Proof. by case: p. Qed. 

Section NilPath.
Context {x : T}.
Hypothesis xG : x \in vertices G.
Program Definition nil_path := @EPath (@GPath x x [::] _ _ _) _.
End NilPath.

Lemma size_path0 (p : epath) : size_path p = 0 <-> src p = dst p.
Proof.
split.
- by move/size0nil; case: p=> -[/= ??? _ _ + _]; move/[swap]; move=> -> /=.
- move=> h; apply/eqP; rewrite size_eq0; apply/eqP; move: h.
  case: p=> -[/= ?? s _ _ <- /andP [+ _]].
  by move/[swap] => ->; case: s=> //= ??; rewrite mem_last.
Qed.

Lemma has_npath0 x : x \in vertices G -> has_npath 0 x x.
Proof. by move=> xG; exists (nil_path xG). Qed.

Lemma has_npath0P (x y : T) : has_npath 0 x y <-> x = y /\ y \in vertices G.
Proof.
split=> [|[->]]; last exact/has_npath0.
case=> -[p /= ?] [[<- <-]] /size_path0 <-; split=> //.
exact: mem_src.
Qed.

Lemma has_npathSP (n : nat) (x y : T):
  has_npath (S n) x y <-> exists2 z, y \in successors G z & has_npath n x z.
Proof.
Admitted.

Lemma has_pathP (x y : T): has_path x y <-> exists n, has_npath n x y.
Proof.
split.
- by case=> p ?; exists (size (walk p)); exists p; split.
- by case=> ? [p []]; exists p.
Qed.

Lemma has_pathxx x : x \in vertices G -> has_path x x.
Proof. move=> xG; apply/has_pathP; exists 0; exact: (has_npath0 xG). Qed.

Lemma epath_vtx (p : epath) : dst p \in vertices G.
Proof.
case: p=> -[x y s /= +++ _]; elim: s x y => /= [|a l IH].
- by move=> x y ? _ <-.
- move=> x y xG /andP [edge_a]; apply/IH.
  move/fsubsetP:(sub_succ xG); apply.
  by rewrite in_succE.
Qed.

Lemma has_path_vtx (x y : T): has_path x y -> y \in vertices G.
Proof. case=> p [_ <-]; exact: epath_vtx. Qed.

Lemma has_npath_vtx n x y: has_npath n x y -> y \in vertices G.
Proof. case=> p [[_ <-]] _; exact: epath_vtx. Qed.

Section EdgePath.
Context {x y : T}.
Hypothesis xG : x \in vertices G.
Hypothesis xGy : edges G x y.
Hypothesis xny : x != y.

Program Definition edge_path := @EPath (@GPath x y [:: y] _ _ _) _.
Next Obligation. by rewrite xGy. Defined.
Next Obligation. by rewrite inE xny. Defined.
End EdgePath.

Lemma has_path_edge x y : x \in vertices G -> edges G x y -> has_path x y.
Proof.
move=> xG xGy; case/boolP: (x == y).
- move/eqP => <-; exact: has_pathxx.
- by move=> xny; exists (edge_path xG xGy xny).
Qed.

Section TransPath.
Context {p p' : epath}.
Hypothesis junction : (dst p) = (src p').

Program Definition trans_path := @EPath (@GPath (src p) (dst p') (shorten (src p) ((walk p) ++ (walk p'))) _ _ _) _.
Next Obligation. by case: p=> -[]. Defined.
Next Obligation.
have: path (edges G) (src p) (walk p ++ walk p') by rewrite cat_path last_dst junction !path_walk.
by case/shortenP.
Defined.
Next Obligation.
have: last (src p) (walk p ++ walk p') = dst p' by rewrite last_cat last_dst junction last_dst.
have: path (edges G) (src p) (walk p ++ walk p') by rewrite cat_path last_dst junction !path_walk.
by case/shortenP.
Defined.
Next Obligation.
have: path (edges G) (src p) (walk p ++ walk p') by rewrite cat_path last_dst junction !path_walk.
by case/shortenP.
Defined.
End TransPath.

Lemma has_path_trans x y z : has_path x y -> has_path y z -> has_path x z.
Proof. by case => [p [? +]] [p' [+ ?]]; move=> <- /esym junc_y; exists (trans_path junc_y); split. Qed. 

Section DFS.
Context (P : T -> Prop).

Lemma ind (x0 : T) :
  P x0
  -> (forall (S : T -> Prop) x,
      (forall x, S x -> P x)
      -> (forall x, S x -> x \in vertices G)
      -> S x -> forall y, y \in successors G x -> P y)
  -> forall y, has_path x0 y -> P y.
Proof.
move=> Px0 PS y /has_pathP[n]; elim: n y => [|n ih] y.
- by move/has_npath0P=> [<-].
case/has_npathSP=> x x0_p_x /[dup] px /ih Px.
apply: (PS (fun y => has_npath n x0 y) x) => //.
exact: has_npath_vtx.
Qed.

End DFS.
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
Hypothesis G1C : commutative (edges G1).
Hypothesis G2C : commutative (edges G2).

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

Lemma foo_haspath:
  {in V1&, forall x y, has_path G1 x y <-> has_path G2 (f x) (f y)}.
Proof.
move=> x y xV1 yV1; split.
- elim/ind.
	+ apply: has_pathxx; move/fsubsetP: f_leq; apply; exact: in_imfset.
	+ move=> S x0 S_path S_vtx S_x0 y0; rewrite in_succE=> x0G1y0.
		admit.
admit.
Admitted.


Lemma bar : gisof G1 G2 f.
Proof.
Admitted.
End Foo.

End IsoProofs.
