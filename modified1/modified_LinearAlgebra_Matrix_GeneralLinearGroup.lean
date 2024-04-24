def det : GL n R →* Rˣ where
  toFun A :=
    { val := (↑A : Matrix n n R).det
      inv := (↑A⁻¹ : Matrix n n R).det
      val_inv := by rw [← det_mul, A.mul_inv, det_one]
      inv_val := by rw [← det_mul, A.inv_mul, det_one] }
  map_one' := Units.ext det_one
  map_mul' A B := Units.ext <| det_mul _ _
#align matrix.general_linear_group.det Matrix.GeneralLinearGroup.det

def toLin : GL n R ≃* LinearMap.GeneralLinearGroup R (n → R) :=
  Units.mapEquiv toLinAlgEquiv'.toMulEquiv
#align matrix.general_linear_group.to_lin Matrix.GeneralLinearGroup.toLin

def mk' (A : Matrix n n R) (_ : Invertible (Matrix.det A)) : GL n R :=
  unitOfDetInvertible A
#align matrix.general_linear_group.mk' Matrix.GeneralLinearGroup.mk'

def mk'' (A : Matrix n n R) (h : IsUnit (Matrix.det A)) : GL n R :=
  nonsingInvUnit A h
#align matrix.general_linear_group.mk'' Matrix.GeneralLinearGroup.mk''

def mkOfDetNeZero {K : Type*} [Field K] (A : Matrix n n K) (h : Matrix.det A ≠ 0) : GL n K :=
  mk' A (invertibleOfNonzero h)
#align matrix.general_linear_group.mk_of_det_ne_zero Matrix.GeneralLinearGroup.mkOfDetNeZero

def toLinear : GeneralLinearGroup n R ≃* LinearMap.GeneralLinearGroup R (n → R) :=
  Units.mapEquiv Matrix.toLinAlgEquiv'.toRingEquiv.toMulEquiv
#align matrix.general_linear_group.to_linear Matrix.GeneralLinearGroup.toLinear

def coeToGL (A : SpecialLinearGroup n R) : GL n R :=
  ⟨↑A, ↑A⁻¹,
    congr_arg ((↑) : _ → Matrix n n R) (mul_right_inv A),
    congr_arg ((↑) : _ → Matrix n n R) (mul_left_inv A)⟩

instance hasCoeToGeneralLinearGroup : Coe (SpecialLinearGroup n R) (GL n R) :=
  ⟨coeToGL⟩
#align matrix.special_linear_group.has_coe_to_general_linear_group Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup

def GLPos : Subgroup (GL n R) :=
  (Units.posSubgroup R).comap GeneralLinearGroup.det
set_option linter.uppercaseLean3 false in
#align matrix.GL_pos Matrix.GLPos

def toGLPos : SpecialLinearGroup n R →* GLPos n R where
  toFun A := ⟨(A : GL n R), show 0 < (↑A : Matrix n n R).det from A.prop.symm ▸ zero_lt_one⟩
  map_one' := Subtype.ext <| Units.ext <| rfl
  map_mul' _ _ := Subtype.ext <| Units.ext <| rfl
set_option linter.uppercaseLean3 false in
#align matrix.special_linear_group.to_GL_pos Matrix.SpecialLinearGroup.toGLPos

def planeConformalMatrix {R} [Field R] (a b : R) (hab : a ^ 2 + b ^ 2 ≠ 0) :
    Matrix.GeneralLinearGroup (Fin 2) R :=
  GeneralLinearGroup.mkOfDetNeZero !![a, -b; b, a] (by simpa [det_fin_two, sq] using hab)
#align matrix.plane_conformal_matrix Matrix.planeConformalMatrix