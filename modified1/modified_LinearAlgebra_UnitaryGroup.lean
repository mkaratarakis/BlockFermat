def toLin' (A : unitaryGroup n α) :=
  Matrix.toLin' A.1
#align matrix.unitary_group.to_lin' Matrix.UnitaryGroup.toLin'

def toLinearEquiv (A : unitaryGroup n α) : (n → α) ≃ₗ[α] n → α :=
  { Matrix.toLin' A.1 with
    invFun := toLin' A⁻¹
    left_inv := fun x =>
      calc
        (toLin' A⁻¹).comp (toLin' A) x = (toLin' (A⁻¹ * A)) x := by rw [← toLin'_mul]
        _ = x := by rw [mul_left_inv, toLin'_one, id_apply]
    right_inv := fun x =>
      calc
        (toLin' A).comp (toLin' A⁻¹) x = toLin' (A * A⁻¹) x := by rw [← toLin'_mul]
        _ = x := by rw [mul_right_inv, toLin'_one, id_apply] }
#align matrix.unitary_group.to_linear_equiv Matrix.UnitaryGroup.toLinearEquiv

def toGL (A : unitaryGroup n α) : GeneralLinearGroup α (n → α) :=
  GeneralLinearGroup.ofLinearEquiv (toLinearEquiv A)
set_option linter.uppercaseLean3 false in
#align matrix.unitary_group.to_GL Matrix.UnitaryGroup.toGL

def embeddingGL : unitaryGroup n α →* GeneralLinearGroup α (n → α) :=
  ⟨⟨fun A => toGL A, toGL_one⟩, toGL_mul⟩
set_option linter.uppercaseLean3 false in
#align matrix.unitary_group.embedding_GL Matrix.UnitaryGroup.embeddingGL

structure on
`Matrix.unitaryGroup n α`, and the embedding into the general linear group
`LinearMap.GeneralLinearGroup α (n → α)`.

We also define the orthogonal group `Matrix.orthogonalGroup n β`, where `β` is a `CommRing`.

## Main Definitions

structure (under multiplication) is inherited from a more general `unitary` construction.
* `Matrix.UnitaryGroup.embeddingGL` is the embedding `Matrix.unitaryGroup n α → GLₙ(α)`, where
  `GLₙ(α)` is `LinearMap.GeneralLinearGroup α (n → α)`.
* `Matrix.orthogonalGroup` is the submonoid of matrices where the transpose is the inverse.

## References

structure on `Matrix.unitaryGroup n` is defined, we show in
`Matrix.UnitaryGroup.toLinearEquiv` that this gives a linear equivalence.
-/
def toLin' (A : unitaryGroup n α) :=
  Matrix.toLin' A.1
#align matrix.unitary_group.to_lin' Matrix.UnitaryGroup.toLin'