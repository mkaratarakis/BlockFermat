def invertibleOfDetInvertible [Invertible A.det] : Invertible A where
  invOf := ⅟ A.det • A.adjugate
  mul_invOf_self := by
    rw [mul_smul_comm, mul_adjugate, smul_smul, invOf_mul_self, one_smul]
  invOf_mul_self := by
    rw [smul_mul_assoc, adjugate_mul, smul_smul, invOf_mul_self, one_smul]
#align matrix.invertible_of_det_invertible Matrix.invertibleOfDetInvertible

def detInvertibleOfLeftInverse (h : B * A = 1) : Invertible A.det where
  invOf := B.det
  mul_invOf_self := by rw [mul_comm, ← det_mul, h, det_one]
  invOf_mul_self := by rw [← det_mul, h, det_one]
#align matrix.det_invertible_of_left_inverse Matrix.detInvertibleOfLeftInverse

def detInvertibleOfRightInverse (h : A * B = 1) : Invertible A.det where
  invOf := B.det
  mul_invOf_self := by rw [← det_mul, h, det_one]
  invOf_mul_self := by rw [mul_comm, ← det_mul, h, det_one]
#align matrix.det_invertible_of_right_inverse Matrix.detInvertibleOfRightInverse

def detInvertibleOfInvertible [Invertible A] : Invertible A.det :=
  detInvertibleOfLeftInverse A (⅟ A) (invOf_mul_self _)
#align matrix.det_invertible_of_invertible Matrix.detInvertibleOfInvertible

def invertibleEquivDetInvertible : Invertible A ≃ Invertible A.det where
  toFun := @detInvertibleOfInvertible _ _ _ _ _ A
  invFun := @invertibleOfDetInvertible _ _ _ _ _ A
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
#align matrix.invertible_equiv_det_invertible Matrix.invertibleEquivDetInvertible

def invertibleOfLeftInverse (h : B * A = 1) : Invertible A :=
  ⟨B, h, mul_eq_one_comm.mp h⟩
#align matrix.invertible_of_left_inverse Matrix.invertibleOfLeftInverse

def invertibleOfRightInverse (h : A * B = 1) : Invertible A :=
  ⟨B, mul_eq_one_comm.mp h, h⟩
#align matrix.invertible_of_right_inverse Matrix.invertibleOfRightInverse

def unitOfDetInvertible [Invertible A.det] : (Matrix n n α)ˣ :=
  @unitOfInvertible _ _ A (invertibleOfDetInvertible A)
#align matrix.unit_of_det_invertible Matrix.unitOfDetInvertible

def (A : Matrix n n α) : A⁻¹ = Ring.inverse A.det • A.adjugate :=
  rfl
#align matrix.inv_def Matrix.inv_def

def invertibleOfIsUnitDet (h : IsUnit A.det) : Invertible A :=
  ⟨A⁻¹, nonsing_inv_mul A h, mul_nonsing_inv A h⟩
#align matrix.invertible_of_is_unit_det Matrix.invertibleOfIsUnitDet

def nonsingInvUnit (h : IsUnit A.det) : (Matrix n n α)ˣ :=
  @unitOfInvertible _ _ _ (invertibleOfIsUnitDet A h)
#align matrix.nonsing_inv_unit Matrix.nonsingInvUnit

def diagonalInvertible {α} [NonAssocSemiring α] (v : n → α) [Invertible v] :
    Invertible (diagonal v) :=
  Invertible.map (diagonalRingHom n α) v
#align matrix.diagonal_invertible Matrix.diagonalInvertible

def invertibleOfDiagonalInvertible (v : n → α) [Invertible (diagonal v)] : Invertible v where
  invOf := diag (⅟ (diagonal v))
  invOf_mul_self :=
    funext fun i => by
      letI : Invertible (diagonal v).det := detInvertibleOfInvertible _
      rw [invOf_eq, diag_smul, adjugate_diagonal, diag_diagonal]
      dsimp
      rw [mul_assoc, prod_erase_mul _ _ (Finset.mem_univ _), ← det_diagonal]
      exact mul_invOf_self _
  mul_invOf_self :=
    funext fun i => by
      letI : Invertible (diagonal v).det := detInvertibleOfInvertible _
      rw [invOf_eq, diag_smul, adjugate_diagonal, diag_diagonal]
      dsimp
      rw [mul_left_comm, mul_prod_erase _ _ (Finset.mem_univ _), ← det_diagonal]
      exact mul_invOf_self _
#align matrix.invertible_of_diagonal_invertible Matrix.invertibleOfDiagonalInvertible

def diagonalInvertibleEquivInvertible (v : n → α) : Invertible (diagonal v) ≃ Invertible v where
  toFun := @invertibleOfDiagonalInvertible _ _ _ _ _ _
  invFun := @diagonalInvertible _ _ _ _ _ _
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
#align matrix.diagonal_invertible_equiv_invertible Matrix.diagonalInvertibleEquivInvertible

def submatrixEquivInvertible (A : Matrix m m α) (e₁ e₂ : n ≃ m) [Invertible A] :
    Invertible (A.submatrix e₁ e₂) :=
  invertibleOfRightInverse _ ((⅟ A).submatrix e₂ e₁) <| by
    rw [Matrix.submatrix_mul_equiv, mul_invOf_self, submatrix_one_equiv]
#align matrix.submatrix_equiv_invertible Matrix.submatrixEquivInvertible

def invertibleOfSubmatrixEquivInvertible (A : Matrix m m α) (e₁ e₂ : n ≃ m)
    [Invertible (A.submatrix e₁ e₂)] : Invertible A :=
  invertibleOfRightInverse _ ((⅟ (A.submatrix e₁ e₂)).submatrix e₂.symm e₁.symm) <| by
    have : A = (A.submatrix e₁ e₂).submatrix e₁.symm e₂.symm := by simp
    -- Porting note: was
    -- conv in _ * _ =>
    --   congr
    --   rw [this]
    rw [congr_arg₂ (· * ·) this rfl]
    rw [Matrix.submatrix_mul_equiv, mul_invOf_self, submatrix_one_equiv]
#align matrix.invertible_of_submatrix_equiv_invertible Matrix.invertibleOfSubmatrixEquivInvertible

def submatrixEquivInvertibleEquivInvertible (A : Matrix m m α) (e₁ e₂ : n ≃ m) :
    Invertible (A.submatrix e₁ e₂) ≃ Invertible A where
  toFun _ := invertibleOfSubmatrixEquivInvertible A e₁ e₂
  invFun _ := submatrixEquivInvertible A e₁ e₂
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
#align matrix.submatrix_equiv_invertible_equiv_invertible Matrix.submatrixEquivInvertibleEquivInvertible