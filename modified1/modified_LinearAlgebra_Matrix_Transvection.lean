def transvection (c : R) : Matrix n n R :=
  1 + Matrix.stdBasisMatrix i j c
#align matrix.transvection Matrix.transvection

def toMatrix (t : TransvectionStruct n R) : Matrix n n R :=
  transvection t.i t.j t.c
#align matrix.transvection_struct.to_matrix Matrix.TransvectionStruct.toMatrix

def inv (t : TransvectionStruct n R) : TransvectionStruct n R where
  i := t.i
  j := t.j
  hij := t.hij
  c := -t.c
#align matrix.transvection_struct.inv Matrix.TransvectionStruct.inv

def sumInl (t : TransvectionStruct n R) : TransvectionStruct (Sum n p) R where
  i := inl t.i
  j := inl t.j
  hij := by simp [t.hij]
  c := t.c
#align matrix.transvection_struct.sum_inl Matrix.TransvectionStruct.sumInl

def reindexEquiv (e : n ≃ p) (t : TransvectionStruct n R) : TransvectionStruct p R where
  i := e t.i
  j := e t.j
  hij := by simp [t.hij]
  c := t.c
#align matrix.transvection_struct.reindex_equiv Matrix.TransvectionStruct.reindexEquiv

def listTransvecCol : List (Matrix (Sum (Fin r) Unit) (Sum (Fin r) Unit) 𝕜) :=
  List.ofFn fun i : Fin r =>
    transvection (inl i) (inr unit) <| -M (inl i) (inr unit) / M (inr unit) (inr unit)
#align matrix.pivot.list_transvec_col Matrix.Pivot.listTransvecCol

def listTransvecRow : List (Matrix (Sum (Fin r) Unit) (Sum (Fin r) Unit) 𝕜) :=
  List.ofFn fun i : Fin r =>
    transvection (inr unit) (inl i) <| -M (inr unit) (inl i) / M (inr unit) (inr unit)
#align matrix.pivot.list_transvec_row Matrix.Pivot.listTransvecRow

structure containing the data of `i, j, c` and a proof that
  `i ≠ j`. These are often easier to manipulate than straight matrices, especially in inductive
  arguments.

* `exists_list_transvec_mul_diagonal_mul_list_transvec` states that any matrix `M` over a field can
  be written in the form `t_1 * ... * t_k * D * t'_1 * ... * t'_l`, where `D` is diagonal and
  the `t_i`, `t'_j` are transvections.

* `diagonal_transvection_induction` shows that a property which is true for diagonal matrices and
  transvections, and invariant under product, is true for all matrices.
* `diagonal_transvection_induction_of_det_ne_zero` is the same statement over invertible matrices.

## Implementation details

structure is useful to use the formalism of
block matrices.

To proceed with the induction, we reindex our matrices to reduce to the above situation.
-/


universe u₁ u₂

namespace Matrix

open Matrix

variable (n p : Type*) (R : Type u₂) {𝕜 : Type*} [Field 𝕜]
variable [DecidableEq n] [DecidableEq p]
variable [CommRing R]

section Transvection

variable {R n} (i j : n)

/-- The transvection matrix `Transvection i j c` is equal to the identity plus `c` at position
`(i, j)`. Multiplying by it on the left (as in `Transvection i j c * M`) corresponds to adding
`c` times the `j`-th line of `M` to its `i`-th line. Multiplying by it on the right corresponds
to adding `c` times the `i`-th column to the `j`-th column. -/
def transvection (c : R) : Matrix n n R :=
  1 + Matrix.stdBasisMatrix i j c
#align matrix.transvection Matrix.transvection

structure containing all the information from which one can build a nontrivial transvection.
This structure is easier to manipulate than transvections as one has a direct access to all the
relevant fields. -/
-- porting note (#5171): removed @[nolint has_nonempty_instance]

structure TransvectionStruct where
  (i j : n)
  hij : i ≠ j
  c : R
#align matrix.transvection_struct Matrix.TransvectionStruct