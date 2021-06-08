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
  let g' := Graph g.[v1 <- Some (v2 |` odflt fset0 (g v1))] in
  Graph g'.[v2 <- Some (v1 |` odflt fset0 (g' v2))].

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

Lemma vtx0 : vertices graph0 = fset0.
Proof. exact: finsupp0. Qed.

Lemma vtx_prop0 (G : graph T) : vertices G != fset0 <-> G != graph0.
Proof.
split; apply/contra_neq.
- by move=> ->; rewrite vtx0.
- case: G=> f; rewrite /vertices /= => h.
  congr Graph; apply/fsfunP=> x /=; rewrite fsfun0E.
  by apply: fsfun_dflt; rewrite h in_fset0.
Qed.

Lemma graph0Pn (G : graph T) : reflect (exists x : T, x \in vertices G) (G != graph0).
Proof.
apply/(iffP idP).
- by move/vtx_prop0/fset0Pn.
- by move=> ?; apply/vtx_prop0/fset0Pn.
Qed.

Lemma in_succE (G : graph T) (x y : T) :
  y \in successors G x = edges G x y.
Proof. by []. Qed.

Lemma edge_vtxl (G : graph T) (x y : T) :
  edges G x y -> x \in vertices G.
Proof.
Admitted.

Lemma edge_vtxr (G : graph T) (x y : T) :
  edges G x y -> y \in vertices G.
Proof.
Admitted.

Lemma sub_succ (G : graph T) (x : T) :
  x \in vertices G -> successors G x `<=` vertices G.
Proof.
Admitted.

Lemma eq_graph (G1 G2 : graph T): G1 = G2 <-> vertices G1 = vertices G2 /\ edges G1 =2 edges G2.
Proof.
split; first by move=> ->.
case: G1=> f; case: G2=> g [Veq Eeq]; congr Graph; apply/fsfunP=> x.
move/fsetP: (Eeq x); move/fsetP: Veq => /(_ x).
rewrite /vertices /successors /=.
case: (finsuppP f x); case: (finsuppP g x)=> //.
by rewrite !mem_finsupp; case: (f x); case: (g x) => //= ?? _ _ _ ->.
Qed.

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
  src  : T;
  dst  : T;
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

(*TODO : créer un lemme d'existence d'un chemin sans cycle : gpath => epath*)
(*TODO : partir d'un gpath qui convient*)

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

Section Ind.
Context (P : T -> Prop).

Lemma has_pathW (x0 : T) :
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

End Ind.
End Connected.

Section Regular.
Context {T : choiceType} (G : graph T) (n : nat).

Definition regular := forall v : T, v \in vertices G -> #|` successors G v| = n.

End Regular.


Section Undirected.
Context {T : choiceType} (G : graph T).
Let V := vertices G.

Lemma edgeC : {in V&, symmetric (edges G)}.
Proof.
Admitted.


Lemma undi_succE : {in V&, forall x y, (x \in successors G y) = (y \in successors G x)}.
Proof. by move=> ????; rewrite !in_succE edgeC. Qed.

Lemma undi_pathP : {in V&, forall x y, has_path G x y -> has_path G y x}.
Proof.
move=> x y xV yV; elim/has_pathW; first exact: has_pathxx.
move=> S x0 S_path S_vtx Sx0 y0 y0_succ; move: (S_vtx _ Sx0)=> x0_vtx.
move/fsubsetP/(_ _ y0_succ) : (sub_succ x0_vtx)=> y0_vtx.
rewrite undi_succE // in_succE in y0_succ.
move: (has_path_edge y0_vtx y0_succ) (S_path _ Sx0); exact: has_path_trans.
Qed.

End Undirected.

(* TODO: sous-graphe *)
(* TODO: image d'un graphe *)

Section ImageGraph.
Context {T1 T2 : choiceType} (G : graph T1) (f : T1 -> T2).
Let V := vertices G.
Let E := edges G.

Definition img_graph := mk_graph (f @` V)
  [rel x y | [exists v : V, [exists w : V, [&& f (val v) == x, f (val w) == y & E (val v) (val w)]]]].

Lemma vtx_img_graph : vertices img_graph = f @` V.
Proof. by rewrite vtx_mk_graph. Qed.

Lemma edge_img_graph x y : reflect (exists2 v, f v = x & (exists2 w, f w = y & E v w)) (edges img_graph x y).
Proof.
rewrite edge_mk_graph /=; apply/(iffP idP).
- case/existsP=> /= v /existsP /= [w] /and3P [fv fw vGw]; exists (fsval v); first exact/eqP.
  by exists (fsval w); first exact/eqP.
- case=> v fv [w fw vGw]; move: (edge_vtxl vGw) (edge_vtxr vGw)=> vV wV.
  by apply/existsP; exists [` vV]; apply/existsP; exists [` wV] => /=; rewrite fv fw !eq_refl.
Qed.

End ImageGraph.

Notation "f '@°' G" := (img_graph G f) (at level 24, format "f  '@°'  G").

Section GIsomorphism.

Context {T1 T2 : choiceType} (G1 : graph T1) (G2 : graph T2).
Let V1 := vertices G1.
Let V2 := vertices G2.
Let E1 := edges G1.
Let E2 := edges G2.

Definition gisof f := {in V1&, injective f} /\ f @° G1 = G2.
Definition giso := exists f, gisof f.

Section IsoProofs.

Lemma gisof_morph f : gisof f -> {in V1&, forall x y, E1 x y = E2 (f x) (f y)}.
Proof.
case=> f_inj f_G1 x y xV1 yV1; rewrite /E2 -f_G1; apply/idP/idP.
- move=> xG1y; apply/edge_img_graph.
  by exists x => //; exists y.
- case/edge_img_graph=> x' + [y' +] x'G1y'.
  move: (edge_vtxl x'G1y') (edge_vtxr x'G1y')=> x'V1 y'V1.
  by move/f_inj => + /f_inj; rewrite xV1 yV1 x'V1 y'V1=> <- // <-.
Qed.

Lemma gisof_bij f : gisof f -> f @` V1 = V2.
Proof. by rewrite /V2; case=> _ <-; rewrite vtx_img_graph. Qed.

Lemma gisofE f:
  gisof f <-> [/\ {in V1&, injective f}, (f @` V1 = V2) &
    {in V1&, forall x y, E1 x y = E2 (f x) (f y)}].
Proof.
split.
- move=> gisoff; split; [by case: gisoff|exact:gisof_bij|exact:gisof_morph].
- case=> f_inj f_bij f_morph; split=> //.
  apply/eq_graph; rewrite vtx_img_graph f_bij; split=> // x y.
  apply/idP/idP.
  + case/edge_img_graph => v <- [w <-] /[dup] /[dup] /edge_vtxl ? /edge_vtxr ?.
    by rewrite -/E2 -f_morph.
  + move=> xG2y; apply/edge_img_graph.
    move: (edge_vtxl xG2y) (edge_vtxr xG2y) (xG2y); rewrite -/V2 -f_bij.
    case/imfsetP => /= v vV1 -> /imfsetP /= [w wV1 ->] ?; exists v => //; exists w => //.
    by rewrite -/E1 f_morph.
Qed.

Lemma gisoE: giso <-> exists f,
  [/\ {in V1&, injective f}, (f @` V1 = V2) &
  {in V1&, forall x y, E1 x y = E2 (f x) (f y)}].
Proof. split; by case=> f /gisofE ?; exists f. Qed.

Section Foo.
Context {f : T1 -> T2}.
Hypothesis f_inj : {in V1&, injective f}.
Hypothesis f_leq : (f @` V1) `<=` V2.
Hypothesis f_morph : {in V1&, forall x y, E1 x y -> E2 (f x) (f y)}.
Hypothesis G2_connected : connected G2.
Hypothesis G_succ : {in V1, forall x, f @` (successors G1 x) = successors G2 (f x)}.
Hypothesis G1_neq0 : G1 != (graph0 T1).

(* TODO: move to enum_proof.v *)
(*Lemma foo_succE:
  {in V1, forall x, f @` (successors G1 x) = (successors G2 (f x))}.
Proof.
move=> x xV1; apply/eqP; rewrite eqEfcard; apply/andP; split.
- apply/fsubsetP=> y /imfsetP [y' /= y'succ ->].
  move/fsubsetP: (sub_succ xV1) => /(_ y' y'succ) y'V1.
  rewrite in_succE; exact: f_morph.
- move/fsubsetP: f_leq => imf.
  rewrite card_in_imfset ?G1_regular ?G2_regular ?imf ?in_imfset //=.
  move/fsubsetP: (sub_succ xV1) => succ1 p q /succ1 pV1 /succ1 qV1; exact: f_inj.
Qed.*)

Lemma foo_has_path : {in V1, forall x, forall y, has_path G2 (f x) y -> y \in f @` V1}.
Proof.
move=> x xV1 y; elim/has_pathW; first exact: in_imfset.
move=> S x0 S_im S_vtx Sx0 y0; case/imfsetP: (S_im _ Sx0) => /= xO' x0'V1 ->.
rewrite -G_succ //; move: y0; exact/fsubsetP/subset_imfset/fsubsetP/sub_succ.
Qed.

Lemma foobar : V2 `<=` f @` V1.
Proof.
apply/fsubsetP=> x xV2; case/graph0Pn : G1_neq0=> y yV1.
by apply: (foo_has_path yV1).
Qed.

Lemma barfoo : {in V1&, forall x y, E2 (f x) (f y) -> E1 x y}.
Proof.
move=> x y xV1 yV1; rewrite -[E2 _ _]in_succE -G_succ // -[E1 _ _]in_succE.
case/imfsetP => y' /= y'_succ /f_inj -> //.
exact: (fsubsetP (sub_succ xV1)).
Qed.

Lemma bar : gisof f.
Proof.
apply/gisofE; split=> //; first by (apply/eqP; rewrite eqEfsubset f_leq foobar).
move=> x y xV1 yV1; apply/idP/idP; first exact: f_morph.
exact: barfoo.
Qed.

End Foo.
End IsoProofs.
End GIsomorphism.

Section GisoTheory.
Context {T1 T2 : choiceType}.

Lemma gisogg (G : graph T1) : giso G G.
Proof. by apply/gisoE; exists id; split=> //; apply/fsetP=> ?; rewrite in_fsetE. Qed.

End GisoTheory.
