Require Import Recdef.
From mathcomp Require Import all_ssreflect all_algebra finmap.
Require Import extra_misc inner_product extra_matrix xorder vector_order row_submx vector_order.
Require Import hpolyhedron polyhedron barycenter poly_base.
Require Import enumeration graph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope ring_scope.

Section Perturbation.

Context (R : realFieldType) (n : nat).
Definition polyhedron := seq lrel[R]_n.

Definition pert (x : R) (m : nat) k : 'cV__:=
  col_mx x%:M (\col_(i < m) if (i == k)%nat then 1 else 0).

Definition perturbation (P : polyhedron) : seq ('cV[R]_n * 'cV[R]__) :=
  let f := fun x => let: [<A, b>] := x.1 in (A, pert b x.2) in
  map f (zip P (ord_enum (size P))).

Lemma size_perturbation P : size (perturbation P) = size P.
Proof.
rewrite size_map size_zip -[X in minn _ X](size_map val) val_ord_enum.
by rewrite size_iota minnn.
Qed.

End Perturbation.
