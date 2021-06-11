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

Lemma edge0 (x y : T) : edges graph0 x y = false.
Proof. by rewrite /edges /successors /= fsfun0E /=. Qed.

Lemma in_succE (G : graph T) (x y : T) :
  y \in successors G x = edges G x y.
Proof. by []. Qed.

Lemma edge_vtxl (G : graph T) (x y : T) :
  edges G x y -> x \in vertices G.
Proof.
rewrite /vertices -in_succE /successors.
by case : (finsuppP G).
Qed.

Lemma edge_vtxr (G : graph T) (x y : T) :
  edges G x y -> y \in vertices G.
Proof.
Admitted. (* TODO : definition of graph ?*)

Lemma sub_succ (G : graph T) (x : T) :
  successors G x `<=` vertices G.
Proof. apply/fsubsetP=> y; rewrite in_succE; exact: edge_vtxr. Qed.

Lemma graphE (G1 G2 : graph T): G1 = G2 <-> vertices G1 = vertices G2 /\ edges G1 =2 edges G2.
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

Lemma edge_mk_graph : {in V&, edges (mk_graph V E) =2 E}.
Proof.
by move=> x y xV yV; rewrite -in_succE /successors /= fsfunE xV /= !inE yV.
Qed.

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
Definition connected := {in (vertices G) &, forall x y : T, has_path x y}.

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
  exact: (edge_vtxr edge_a).
Qed.

Lemma has_path_vtx (x y : T): has_path x y -> y \in vertices G.
Proof. case=> p [_ <-]; exact: epath_vtx. Qed.

Lemma has_npath_vtx n x y: has_npath n x y -> y \in vertices G.
Proof. case=> p [[_ <-]] _; exact: epath_vtx. Qed.

Section EdgePath.
Context {x y : T}.
Hypothesis xGy : edges G x y.
Hypothesis xny : x != y.

Program Definition edge_path := @EPath (@GPath x y [:: y] _ _ _) _.
Next Obligation. exact: (edge_vtxl xGy). Defined.
Next Obligation. by rewrite xGy. Defined.
Next Obligation. by rewrite inE xny. Defined.
End EdgePath.

Lemma has_path_edge x y : edges G x y -> has_path x y.
Proof.
move=> xGy; case/boolP: (x == y).
- move/eqP => ->; exact/has_pathxx/(edge_vtxr xGy).
- by move=> xny; exists (edge_path xGy xny).
Qed.

Section TransPath.
Context {p p' : epath}.
Hypothesis junction : (dst p) = (src p').

(*TODO : créer un lemme d'existence d'un chemin sans cycle : gpath => epath*)
(*TODO : partir d'un gpath qui convient*)

Program Definition trans_path :=
  @EPath (@GPath (src p) (dst p') (shorten (src p) ((walk p) ++ (walk p'))) _ _ _) _.
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

Section BelastPath.
Context (p : epath).
Let bwalk := (behead (belast (src p) (walk p))).

Program Definition belast_path :=
  @EPath (@GPath (src p) (last (src p) bwalk) bwalk _ _ _) _.
Next Obligation. exact: mem_src. Defined.
Next Obligation.
  move: (path_walk p); rewrite /bwalk. elim/last_ind: (walk p)=> //= l a _.
  by rewrite belast_rcons /= rcons_path=> /andP [].
Defined.
Next Obligation.
  move: (uniq_walk p); rewrite /= /bwalk; elim/last_ind: (walk p) => // l a _.
  rewrite belast_rcons /= rcons_uniq mem_rcons inE negb_or -!andbA.
  by case/and4P => _ -> _ ->.
Defined.

Lemma dst_blpath : dst belast_path = last (src p) (bwalk).
Proof. by []. Qed.

Lemma blpath_edge_last : walk p != [::] ->
  edges G (dst belast_path) (dst p).
Proof.
rewrite dst_blpath /bwalk; move: (last_dst p) (path_walk p).
elim/last_ind: (walk p)=> //= l a _.
by rewrite last_rcons rcons_path belast_rcons /=; move=> -> /andP [].
Qed.

Lemma src_blpath : src belast_path = src p. Proof. by []. Qed.

Lemma size_blpath : size_path belast_path = (size_path p).-1.
Proof.
rewrite /size_path /= /bwalk.
by elim/last_ind: (walk p)=> //= l a _; rewrite belast_rcons size_rcons /=.
Qed.

End BelastPath.

Lemma has_npathSP (n : nat) (x y : T):
  has_npath (S n) x y -> exists2 z, y \in successors G z & has_npath n x z.
Proof.
case=> p [[<- <-]] size_p; set bp := (belast_path p).
exists (dst bp).
+ apply: blpath_edge_last; apply/negP; rewrite -size_eq0.
  by rewrite /size_path in size_p; rewrite size_p. (* TODO : ugly *)
+ by exists bp; split; first split=> //; rewrite size_blpath size_p.
Qed.

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
move: (edge_vtxr y0_succ)=> y0_vtx.
rewrite undi_succE // in_succE in y0_succ.
move: (has_path_edge y0_succ) (S_path _ Sx0); exact: has_path_trans.
Qed.

End Undirected.

(* TODO: sous-graphe *)
(* TODO: image d'un graphe *)

Section ImageGraph.
Context {T1 T2 : choiceType} (G : graph T1) (f : T1 -> T2).
Let V := vertices G.
Let E := edges G.

Definition img_graph := mk_graph (f @` V)
  [rel x y | [exists v : V, [exists w : V,
  [&& f (val v) == x, f (val w) == y & E (val v) (val w)]]]].

Lemma vtx_img_graph : vertices img_graph = f @` V.
Proof. by rewrite vtx_mk_graph. Qed.

Lemma edge_img_graph x y : reflect
  (exists2 v, f v = x & (exists2 w, f w = y & E v w))
  (edges img_graph x y).
Proof.
apply/(iffP idP).
- move/[dup]/[dup] => /edge_vtxl + /edge_vtxr.
  rewrite vtx_img_graph=> xV2 yV2; rewrite edge_mk_graph //=.
  case/existsP=> x' /existsP [y'] /and3P [/eqP <- /eqP <- x'Gy'].
  by exists (fsval x')=> //; exists (fsval y').
- case=> x' fx' [y' fy' /[dup] /[dup] x'Gy' /edge_vtxl x'G /edge_vtxr y'G].
  rewrite edge_mk_graph /= -?fx' -?fy' ?in_imfset //.
  apply/existsP; exists [` x'G]; apply/existsP; exists [` y'G].
  by rewrite !eq_refl x'Gy'.
Qed.

End ImageGraph.

Notation "f '@°' G" := (img_graph G f) (at level 24, format "f  '@°'  G").

Section ImgTheory.
Context {T1 T2 T3 : choiceType} (f : T1 -> T2) (g : T2 -> T3).
Lemma img_graph0 : f @° (graph0 T1) = graph0 T2.
Proof.
apply/graphE; split.
- rewrite vtx_img_graph !vtx0; apply/fsetP=> x; apply/idP/idP/negP.
  by case/imfsetP.
- move=> x y; rewrite edge0.
  apply/(introF (edge_img_graph (graph0 T1) f x y)).
  by case=> ? _ [? _]; rewrite edge0.
Qed.

Lemma comp_img_graph (G : graph T1) : (g \o f) @° G = g @° (f @° G).
Proof.
apply/graphE; split.
- rewrite !vtx_img_graph; apply/fsetP=> x; apply/idP/idP.
  + by case/imfsetP=> /= x0 x0G ->; apply/in_imfset/in_imfset.
  + case/imfsetP=> /= x0 /imfsetP [/= x1 x1G -> ->]; apply/imfsetP.
    by exists x1.
- move=> x y; apply/idP/idP.
  + case/edge_img_graph=> x' <- [y' <- x'Gy']; apply/edge_img_graph.
    exists (f x')=> //; exists (f y')=> //; apply/edge_img_graph.
    by exists x'=> //; exists y'.
  + case/edge_img_graph=> x' <- [y' <- /edge_img_graph [x'' <- [y'' <- xGy'']]].
    by apply/edge_img_graph; exists x''=> //; exists y''.
Qed.

End ImgTheory.

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
  apply/graphE; rewrite vtx_img_graph f_bij; split=> // x y.
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
apply/(foo_has_path yV1)/G2_connected=> //.
by move/fsubsetP: f_leq; apply; rewrite in_imfset.
Qed.

Lemma barfoo : {in V1&, forall x y, E2 (f x) (f y) -> E1 x y}.
Proof.
move=> x y xV1 yV1; rewrite -[E2 _ _]in_succE -G_succ // -[E1 _ _]in_succE.
case/imfsetP => y' /= y'_succ /f_inj -> //.
exact: (edge_vtxr y'_succ).
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

Module XFinmap.
Section XFinmap.
Context {T1 T2: choiceType} (f : T1 -> T2) (S1 : {fset T1}) (x0 : T1).
Let S2 := f @` S1.
Hypothesis f_inj : {in S1&, injective f}.

Section EmptyS1.
Hypothesis S1_eq0: S1 = fset0.
Lemma emptyS2 : S2 = fset0.
Proof.
apply/fsetP=> x; rewrite in_fset0 /S2.
by apply/(introF (imfsetP _ f _ _))=> -[/= x']; rewrite S1_eq0.
Qed.

Definition g_empty := fun _ : T2 => x0.
Lemma g_emptyK : {in S1, cancel f g_empty}.
Proof. by move=> x; rewrite S1_eq0. Qed.
Lemma g_emptyKd : {in S2, cancel g_empty f}.
Proof. by move=> x; rewrite emptyS2. Qed.

End EmptyS1.
Section NotEmpty.
Hypothesis S1_neq0 : S1 != fset0.
Let x1 := [` xchooseP (fset0Pn _ S1_neq0) ].


Lemma tmp : f (val x1) \in S2. Proof. exact/in_imfset/valP. Qed.
Definition fS : S1 -> S2 := fun x=> insubd [` tmp] (f (val x)).
Lemma has_inv (y : S2) : exists x, fS x == y.
Proof. 
case/imfsetP: (valP y)=> /= x xS1 y_eq; exists [` xS1].
by rewrite -val_eqE val_insubd /= in_imfset ?y_eq.
Qed.
Definition fS_inv (y : S2) := xchoose (has_inv y).
Definition f_inv (y : T2) := val (fS_inv (insubd [`tmp ] y)).

Lemma fS_inj : injective fS.
Proof.
move=> x y /(congr1 val); rewrite !insubdK ?in_imfset ?(valP x) ?(valP y) //.
move/f_inj=> /(_ (valP x) (valP y)); exact: val_inj.
Qed.

Lemma fSK : cancel fS fS_inv.
Proof.
move=> x.
move/eqP : (xchooseP (has_inv (fS x))); exact: fS_inj.
Qed.

Lemma fSKd : cancel fS_inv fS.
Proof.
move=> x; exact/eqP/(xchooseP (has_inv x)).
Qed.

Lemma fK : {in S1, cancel f f_inv}.
Proof.
move=> x xS1.
have ->: x = val [`xS1] by []; congr val.
exact/fSK.
Qed.

Lemma fKd : {in S2, cancel f_inv f}.
Proof. by move=> x /imfsetP [/= y yS1 ->]; rewrite fK. Qed.

End NotEmpty.
End XFinmap.
End XFinmap.

Section Bijections.

Context {T1 T2: choiceType} (f : T1 -> T2) (S1 : {fset T1}) (x0 : T1).
Hypothesis f_inj : {in S1 &, injective f}.
Let S2 := f @` S1.

Lemma in_bij : exists2 g, {in S1, cancel f g} & {in S2, cancel g f}.
Proof.
case/boolP: (S1 == fset0).
- move/eqP => S1_eq0; exists (XFinmap.g_empty x0).
  + exact: XFinmap.g_emptyK.
  + exact: XFinmap.g_emptyKd.
- move=> S1_neq0; exists (XFinmap.f_inv f S1_neq0).
  + exact: (XFinmap.fK).
  + exact: (XFinmap.fKd).
Qed.

Lemma in_inv : exists2 g, {in S2 &, injective g} & g @` S2 = S1.
Proof.
case: in_bij=> g can_fg can_gf; exists g.
- move=> x y /imfsetP [/= x' x'S1 ->] /imfsetP [/= y' y'S1 ->].
  by rewrite !can_fg // => ->.
- apply/fsetP=> x; apply/idP/idP.
  + case/imfsetP=> /= x' /imfsetP [/= x'' x''S1 ->] ->.
    by rewrite can_fg.
  + by move=> xS1; apply/imfsetP=> /=; exists (f x); rewrite ?in_imfset ?can_fg.
Qed.

End Bijections.


Section GisoTheory.

Lemma gisogg {T : choiceType} (G : graph T) : giso G G.
Proof. by apply/gisoE; exists id; split=> //; apply/fsetP=> ?; rewrite in_fsetE. Qed.

Lemma giso0n {T1 T2 : choiceType} (G1 : graph T1) (G2 : graph T2) :
  giso G1 G2 -> G1 != (graph0 T1) -> G2 != (graph0 T2).
Proof.
case=> f [f_inj] => <-.
case/graph0Pn=> x xV1; apply/graph0Pn; exists (f x).
by rewrite vtx_img_graph in_imfset.
Qed.

Lemma giso00 {T1 T2 : choiceType} (f: T1 -> T2) : giso (graph0 T1) (graph0 T2).
Proof. by exists f; split; rewrite ?img_graph0 //; move=> x y; rewrite vtx0. Qed. 

Lemma giso_sym {T1 T2 : choiceType} (G1 : graph T1) (G2 : graph T2) (x0 : T1):
  giso G1 G2 -> giso G2 G1.
Proof.
move=> /gisoE [f [f_inj f_surj f_morph]].
apply/gisoE; case: (in_bij x0 f_inj)=> g can_fg can_gf.
exists g; split; rewrite -f_surj.
- move=> x y /imfsetP [/= x' x'V1 ->] /imfsetP [/= y' y'V1 ->].
  by rewrite !can_fg // => ->.
- apply/fsetP=> x; apply/idP/idP.
  + by case/imfsetP=> /= x' /imfsetP [/= x'' ? -> ->]; rewrite can_fg.
  + by move=> xV1; apply/imfsetP; exists (f x); rewrite ?in_imfset ?can_fg.
- move=> x y /imfsetP [/= x' x'V1 ->] /imfsetP [/= y' y'V1 ->].
  by rewrite !can_fg -?f_morph.
Qed.

Lemma giso_trans {T1 T2 T3 : choiceType}
  (G1 : graph T1) (G2 : graph T2) (G3 : graph T3) :
  giso G1 G2 -> giso G2 G3 -> giso G1 G3.
Proof.
case=> f [f_inj <-] [g [g_inj <-]]; exists (g \o f); split.
- move=> x y xV1 yV1 /= /g_inj /f_inj.
  by apply; rewrite ?vtx_img_graph ?in_imfset.
- by rewrite comp_img_graph.
Qed.

Lemma gisof_has_path {T1 T2 : choiceType}
  (G1 : graph T1) (G2 : graph T2) f x y :
  gisof G1 G2 f -> x \in vertices G1 ->
  has_path G1 x y -> has_path G2 (f x) (f y).
Proof.
case => f_inj <- xG1.
elim/has_pathW.
- by apply/has_pathxx; rewrite vtx_img_graph in_imfset.
- move=> S x0 S_path S_vtx /[dup] /S_path xG_x0 /S_vtx x0G y0 x0Gy0.
  apply/(has_path_trans xG_x0)/has_path_edge.
  + by apply/edge_img_graph; exists x0=> //; exists y0.
Qed.

Lemma giso_connected {T1 T2 : choiceType} (G1 : graph T1) (G2 : graph T2) :
  giso G1 G2 -> connected G1 -> connected G2.
Proof.
case=> f /[dup] -[f_inj <-] /gisof_has_path Hpath G1_conn x y.
rewrite vtx_img_graph=> /imfsetP [/= x' x'G1 ->] /imfsetP [/= y' y'G1 ->].
apply/Hpath=> //; exact/G1_conn.
Qed.

Lemma gisof_succ {T1 T2 : choiceType} (G1 : graph T1) (G2 : graph T2) f x:
  gisof G1 G2 f -> x \in vertices G1 ->
  successors G2 (f x) = f @` (successors G1 x).
Proof.
case=> f_inj <- xG1; apply/fsetP=> y; rewrite in_succE; apply/idP/idP.
- case/edge_img_graph=> x' + [y' <-] /[dup] /edge_vtxl x'G1.
  by move/f_inj=> <- // ?; apply/in_imfset.
- case/imfsetP=> /= y' xGy' ->; apply/edge_img_graph.
  by exists x=> //; exists y'.
Qed.

Lemma giso_regular {T1 T2 : choiceType} (G1 : graph T1) (G2 : graph T2) n :
  giso G1 G2 -> regular G1 n -> regular G2 n.
Proof.
case=> f /[dup] -[f_inj <-] /gisof_succ Hsucc G1_reg x.
rewrite vtx_img_graph=> /imfsetP [/= x' x'G1 ->].
rewrite Hsucc // card_in_imfset /= ?(G1_reg x') //.
move=> v w; rewrite !in_succE; move/edge_vtxr=> + /edge_vtxr.
exact: f_inj.
Qed.

End GisoTheory.
