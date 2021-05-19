Require Import Recdef.
From mathcomp Require Import all_ssreflect all_algebra finmap.
Require Import extra_misc inner_product extra_matrix xorder vector_order row_submx vector_order.
Require Import hpolyhedron polyhedron barycenter poly_base.
Require Import enumeration graph MapFold enumEquiv.
Require Import high_graph.
From Bignums Require Import BigQ.
Require Import Setoid.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory.
Import GRing.Theory Num.Theory.

Open Scope ring_scope.

Section Perturbation.

Context {n' : nat} (n := n'.+1) (base : base_t[rat,n]).

Definition create_perturbation {m : nat} (b : rat) (k : 'I_m) : 'rV_m.+1 :=
  @row_mx _ _ 1 m (const_mx b) (row k (- pid_mx m)).


Definition perturbation :=
  map
  (fun x: lrel * 'I_(#|`base|) => (x.1.1^T , create_perturbation x.1.2 x.2))
  (zip (enum_fset base) (ord_enum #|`base|)).

(*TODO A-t-on x \in P : {poly base} => x \in perturbation ? Même chose avec des sommets ?*)

End Perturbation.

Section LexiBasis.

Context {n m: nat} (base_p : seq ('rV[rat]_n * 'rV[rat]_m.+1)).
Hypothesis base_size: size base_p = m.

Definition all_sat (x : 'M[rat]_(n,m.+1)) :=
  all (fun l => sat_ineq l x) base_p.

Definition sat_mask (mas : bitseq) (x : 'M[rat]_(n, m.+1)) :=
  all (fun l => sat_ineq l x) (mask mas base_p).

Definition eq_mask (mas : bitseq) (x : 'M[rat]_(n, m.+1)) :=
  all (fun l => sat_eq l x) (mask mas base_p).

Definition lexi_preaxiom (b : (bitseq * 'M[rat]_(n,m.+1))%type) :=
  [&& all_sat b.2, card_bitseq b.1 == n,
    size b.1 == m & eq_mask b.1 b.2].

Record lexi_prebasis := Lexi {
  prebase :> (bitseq * 'M[rat]_(n,m.+1))%type;
  preaxiom : lexi_preaxiom prebase
}.

Definition lexi_mask (L : lexi_prebasis) : bitseq := L.1.
Definition lexi_point (L : lexi_prebasis) : 'M[rat]_(n, m.+1) := L.2.
  
Canonical prelexi_subType := [subType for prebase].
Definition prelexi_eqMixin := [eqMixin of lexi_prebasis by <:].
Canonical prelexi_eqType := EqType _ prelexi_eqMixin.
Definition prelexi_choiceMixin := [choiceMixin of lexi_prebasis by <:].
Canonical prelexi_choiceType := ChoiceType _ prelexi_choiceMixin.

Lemma lexi_preaxiomP (L : lexi_prebasis) :
  lexi_preaxiom L.
Proof. exact: preaxiom. Qed.

Lemma lexi_all_sat (L : lexi_prebasis) :
  all_sat (lexi_point L).
Proof. by case/and4P: (lexi_preaxiomP L). Qed.

Lemma lexi_card (L : lexi_prebasis) :
  card_bitseq (lexi_mask L) = n.
Proof. by apply/eqP; case/and4P: (lexi_preaxiomP L). Qed.

Lemma lexi_size (L : lexi_prebasis) :
  size (lexi_mask L) = m.
Proof. by apply/eqP; case/and4P : (lexi_preaxiomP L). Qed.

Lemma lexi_eq_mask (L: lexi_prebasis) :
  eq_mask (lexi_mask L) (lexi_point L).
Proof. by case/and4P: (lexi_preaxiomP L). Qed.

Lemma lexi_sat_maskP (L: lexi_prebasis) x:
  all_sat x -> sat_mask (lexi_mask L) x.
Proof. move=> ?; exact: all_mask. Qed.

Definition lexi_matrix (L : lexi_prebasis) : 'M_n :=
  \matrix_(i < n) (mask (lexi_mask L) (unzip1 base_p))`_i.

Definition lexi_aff (L : lexi_prebasis) : 'M_(n, m.+1) :=
  \matrix_(i < n) (mask (lexi_mask L) (unzip2 base_p))`_i.

Lemma lexi_mtx_affP (L : lexi_prebasis) x:
  reflect
  ((lexi_matrix L) *m x = (lexi_aff L))
  (eq_mask (lexi_mask L) x).
Proof.
apply/(iffP idP).
- move/allP=> /= h; apply/row_matrixP => i.
  rewrite row_mul !rowK -!map_mask.
  set s:= mask _ _ in h *.
  have sz_s : size s = n by
  rewrite size_mask ?lexi_size ?base_size -?(lexi_card L).
  move: (ltn_ord i); rewrite -{2}sz_s=> i_lt.
  move/eqP: (h s`_i (mem_nth _ i_lt)).
  congr (_ = _); first congr (_ *m _); exact/esym/nth_map.
- move/row_matrixP=> h; apply/allP => l /nthP /= /(_ 0) [i i_lt <-].
  set s := mask _ _ in i_lt *.
  have sz_s : size s = n by
  rewrite size_mask ?lexi_size ?base_size -?(lexi_card L).
  rewrite sz_s in i_lt; move: (h (Ordinal i_lt)).
  rewrite row_mul !rowK -!map_mask !(nth_map 0) ?sz_s //=.
  by move/eqP.
Qed.



Lemma lexi_solP (L: lexi_prebasis):
  (lexi_matrix L) *m (lexi_point L) = (lexi_aff L).
Proof. exact/lexi_mtx_affP/lexi_eq_mask. Qed.

Lemma lexi_mtx_satP (L: lexi_prebasis) x:
  sat_mask (lexi_mask L) x ->
  forall i, ((row i (lexi_matrix L)) *m x) >=lex (row i (lexi_aff L)).
Proof.
move/allP=> /= sat_x i; rewrite !rowK -!map_mask.
move: (ltn_ord i). rewrite -[in X in (_ < X)%nat -> _](lexi_card L)=> size_m.
rewrite !(nth_map 0) ?size_mask ?lexi_size ?base_size //.
by apply/sat_x/mem_nth; rewrite size_mask ?lexi_size ?base_size.
Qed.

 
(* ------------------------------------------------------------------- *)

Definition is_basis (L : lexi_prebasis) : bool :=
  (lexi_matrix L) \in unitmx.

Record lexi_basis := LexiB
  {
    lbase :> lexi_prebasis;
    lbase_is_basis : is_basis lbase
  }.

Canonical lexi_subType := [subType for lbase].
Definition lexi_eqMixin := [eqMixin of lexi_basis by <:].
Canonical lexi_eqType := EqType _ lexi_eqMixin.
Definition lexi_choiceMixin := [choiceMixin of lexi_basis by <:].
Canonical lexi_choiceType := ChoiceType _ lexi_choiceMixin.

Lemma lexi_basisP (L : lexi_basis) : is_basis L.
Proof. by case: L. Qed.

Lemma lexi_pointP (L : lexi_basis) M:
  eq_mask (lexi_mask L) M -> M = (lexi_point L).
Proof.
move : (lexi_solP L) => + /lexi_mtx_affP; move=> <-.
apply: row_full_inj; rewrite row_full_unit; exact: lexi_basisP.
Qed.

End LexiBasis.

Section LexPivot.

Context {n m: nat} (base_p : seq ('rV[rat]_n * 'rV[rat]_m.+1)).
Hypothesis base_size: size base_p = m.
Hypothesis base_uniq : uniq base_p.

Context (v : 'M[rat]_(n,m.+1)) (d : 'cV[rat]_n).


Definition direction_mask :=
  [seq ((x.1 *m d) 0 0) < 0 | x <- base_p].

Definition direction_unfeasible :=
  seq.has id direction_mask.

Definition gap_d (x : ('rV[rat]_n * 'rV[rat]_m.+1)) :=
  ((x.1 *m d) 0 0)^-1 *: (x.2 - (x.1 *m v)).


Definition gaps :=
  [seq gap_d x| x <- (mask direction_mask base_p)].

Definition min_gap := lex_min_seq gaps.

Definition along_dir := v + d *m min_gap.

Hypothesis dirN : direction_unfeasible.
Hypothesis sat_v : all_sat base_p v.


Lemma gapsN0 : gaps != [::].
Proof.
rewrite /gaps -size_eq0 size_map size_mask ?size_map //; move: dirN.
rewrite /direction_unfeasible has_count; exact: lt0n_neq0.
Qed.


Lemma min_gap_ge0: min_gap >=lex 0.
Proof.
rewrite /min_gap.
move/has_nthP: (lex_min_seq_eq gapsN0)=> /= /(_ 0) [i + /eqP ->].
rewrite /gaps -filter_mask size_map size_filter => i_ord.
set s := [seq _ | _ <- _ & _ ].
move: (@mem_nth _ 0 s i).
have ilts: (i < size s)%nat by rewrite size_map size_filter.
case/(_ ilts)/mapP => /= x; rewrite mem_filter=> /andP [x_dir x_base] ->.
apply: lex_scalar_le0.
- by rewrite invr_le0 (ltW x_dir).
- rewrite lex_subr_le0; move/allP: sat_v; exact.
Qed.

Lemma min_gapP b: b \in base_p -> ((b.1 *m d) 0 0) < 0 ->
  min_gap <=lex (gap_d b).
Proof.
move=> base_b b_dir; apply/lex_min_seq_ler/map_f.
by rewrite -filter_mask mem_filter base_b b_dir.
Qed.


Lemma along_dirP: all_sat base_p along_dir.
Proof.
apply/allP=> b b_base_p.
rewrite /sat_ineq /along_dir mulmxDr mulmxA.
have ->: b.1 *m d *m min_gap = ((b.1 *m d) 0 0) *: min_gap.
- by apply/matrixP=> i j; rewrite !mxE (ord1_eq0 i) /= big_ord1 !mxE.
case: (ltrgt0P ((b.1 *m d) 0 0)).
- move=> h.
  move/(lex0_nnscalar (ltW h)): (min_gap_ge0) => dir_ge0.
  move/allP: sat_v=> /(_ b b_base_p) => sat_b.
  by move: (lex_add sat_b dir_ge0); rewrite addr0.
- move=> h; move: (min_gapP b_base_p h).
  rewrite (lex_negscalar _ _ h) -(lex_add2l (b.1 *m v)).
  rewrite scalerA mulrV ?unitf_lt0 //.
  by rewrite scale1r addrCA addrN addr0.
- move=> ->; rewrite scale0r addr0.
  move/allP: sat_v; exact.
Qed.









