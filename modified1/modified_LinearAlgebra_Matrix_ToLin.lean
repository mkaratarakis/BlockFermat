def Matrix.vecMulLinear [Fintype m] (M : Matrix m n R) : (m → R) →ₗ[R] n → R where
  toFun x := x ᵥ* M
  map_add' _ _ := funext fun _ ↦ add_dotProduct _ _ _
  map_smul' _ _ := funext fun _ ↦ smul_dotProduct _ _ _
#align matrix.vec_mul_linear Matrix.vecMulLinear

def LinearMap.toMatrixRight' : ((m → R) →ₗ[R] n → R) ≃ₗ[Rᵐᵒᵖ] Matrix m n R where
  toFun f i j := f (stdBasis R (fun _ ↦ R) i 1) j
  invFun := Matrix.vecMulLinear
  right_inv M := by
    ext i j
    simp only [Matrix.vecMul_stdBasis, Matrix.vecMulLinear_apply]
  left_inv f := by
    apply (Pi.basisFun R m).ext
    intro j; ext i
    simp only [Pi.basisFun_apply, Matrix.vecMul_stdBasis, Matrix.vecMulLinear_apply]
  map_add' f g := by
    ext i j
    simp only [Pi.add_apply, LinearMap.add_apply, Matrix.add_apply]
  map_smul' c f := by
    ext i j
    simp only [Pi.smul_apply, LinearMap.smul_apply, RingHom.id_apply, Matrix.smul_apply]
#align linear_map.to_matrix_right' LinearMap.toMatrixRight'

def Matrix.toLinearEquivRight'OfInv [Fintype n] [DecidableEq n] {M : Matrix m n R}
    {M' : Matrix n m R} (hMM' : M * M' = 1) (hM'M : M' * M = 1) : (n → R) ≃ₗ[R] m → R :=
  { LinearMap.toMatrixRight'.symm M' with
    toFun := Matrix.toLinearMapRight' M'
    invFun := Matrix.toLinearMapRight' M
    left_inv := fun x ↦ by
      rw [← Matrix.toLinearMapRight'_mul_apply, hM'M, Matrix.toLinearMapRight'_one, id_apply]
    right_inv := fun x ↦ by
      dsimp only -- Porting note: needed due to non-flat structures
      rw [← Matrix.toLinearMapRight'_mul_apply, hMM', Matrix.toLinearMapRight'_one, id_apply] }
#align matrix.to_linear_equiv_right'_of_inv Matrix.toLinearEquivRight'OfInv

def Matrix.mulVecLin [Fintype n] (M : Matrix m n R) : (n → R) →ₗ[R] m → R where
  toFun := M.mulVec
  map_add' _ _ := funext fun _ ↦ dotProduct_add _ _ _
  map_smul' _ _ := funext fun _ ↦ dotProduct_smul _ _ _
#align matrix.mul_vec_lin Matrix.mulVecLin

def LinearMap.toMatrix' : ((n → R) →ₗ[R] m → R) ≃ₗ[R] Matrix m n R where
  toFun f := of fun i j ↦ f (stdBasis R (fun _ ↦ R) j 1) i
  invFun := Matrix.mulVecLin
  right_inv M := by
    ext i j
    simp only [Matrix.mulVec_stdBasis, Matrix.mulVecLin_apply, of_apply]
  left_inv f := by
    apply (Pi.basisFun R n).ext
    intro j; ext i
    simp only [Pi.basisFun_apply, Matrix.mulVec_stdBasis, Matrix.mulVecLin_apply, of_apply]
  map_add' f g := by
    ext i j
    simp only [Pi.add_apply, LinearMap.add_apply, of_apply, Matrix.add_apply]
  map_smul' c f := by
    ext i j
    simp only [Pi.smul_apply, LinearMap.smul_apply, RingHom.id_apply, of_apply, Matrix.smul_apply]
#align linear_map.to_matrix' LinearMap.toMatrix'

def Matrix.toLin' : Matrix m n R ≃ₗ[R] (n → R) →ₗ[R] m → R :=
  LinearMap.toMatrix'.symm
#align matrix.to_lin' Matrix.toLin'

def Matrix.toLin'OfInv [Fintype m] [DecidableEq m] {M : Matrix m n R} {M' : Matrix n m R}
    (hMM' : M * M' = 1) (hM'M : M' * M = 1) : (m → R) ≃ₗ[R] n → R :=
  { Matrix.toLin' M' with
    toFun := Matrix.toLin' M'
    invFun := Matrix.toLin' M
    left_inv := fun x ↦ by rw [← Matrix.toLin'_mul_apply, hMM', Matrix.toLin'_one, id_apply]
    right_inv := fun x ↦ by
      simp only
      rw [← Matrix.toLin'_mul_apply, hM'M, Matrix.toLin'_one, id_apply] }
#align matrix.to_lin'_of_inv Matrix.toLin'OfInv

def LinearMap.toMatrixAlgEquiv' : ((n → R) →ₗ[R] n → R) ≃ₐ[R] Matrix n n R :=
  AlgEquiv.ofLinearEquiv LinearMap.toMatrix' LinearMap.toMatrix'_one LinearMap.toMatrix'_mul
#align linear_map.to_matrix_alg_equiv' LinearMap.toMatrixAlgEquiv'

def Matrix.toLinAlgEquiv' : Matrix n n R ≃ₐ[R] (n → R) →ₗ[R] n → R :=
  LinearMap.toMatrixAlgEquiv'.symm
#align matrix.to_lin_alg_equiv' Matrix.toLinAlgEquiv'

def LinearMap.toMatrix : (M₁ →ₗ[R] M₂) ≃ₗ[R] Matrix m n R :=
  LinearEquiv.trans (LinearEquiv.arrowCongr v₁.equivFun v₂.equivFun) LinearMap.toMatrix'
#align linear_map.to_matrix LinearMap.toMatrix

def Matrix.toLin : Matrix m n R ≃ₗ[R] M₁ →ₗ[R] M₂ :=
  (LinearMap.toMatrix v₁ v₂).symm
#align matrix.to_lin Matrix.toLin

def Matrix.toLinOfInv [DecidableEq m] {M : Matrix m n R} {M' : Matrix n m R} (hMM' : M * M' = 1)
    (hM'M : M' * M = 1) : M₁ ≃ₗ[R] M₂ :=
  { Matrix.toLin v₁ v₂ M with
    toFun := Matrix.toLin v₁ v₂ M
    invFun := Matrix.toLin v₂ v₁ M'
    left_inv := fun x ↦ by rw [← Matrix.toLin_mul_apply, hM'M, Matrix.toLin_one, id_apply]
    right_inv := fun x ↦ by
      simp only
      rw [← Matrix.toLin_mul_apply, hMM', Matrix.toLin_one, id_apply] }
#align matrix.to_lin_of_inv Matrix.toLinOfInv

def LinearMap.toMatrixAlgEquiv : (M₁ →ₗ[R] M₁) ≃ₐ[R] Matrix n n R :=
  AlgEquiv.ofLinearEquiv
    (LinearMap.toMatrix v₁ v₁) (LinearMap.toMatrix_one v₁) (LinearMap.toMatrix_mul v₁)
#align linear_map.to_matrix_alg_equiv LinearMap.toMatrixAlgEquiv

def Matrix.toLinAlgEquiv : Matrix n n R ≃ₐ[R] M₁ →ₗ[R] M₁ :=
  (LinearMap.toMatrixAlgEquiv v₁).symm
#align matrix.to_lin_alg_equiv Matrix.toLinAlgEquiv

def leftMulMatrix : S →ₐ[R] Matrix m m R where
  toFun x := LinearMap.toMatrix b b (Algebra.lmul R S x)
  map_zero' := by
    dsimp only  -- porting node: needed due to new-style structures
    rw [AlgHom.map_zero, LinearEquiv.map_zero]
  map_one' := by
    dsimp only  -- porting node: needed due to new-style structures
    rw [AlgHom.map_one, LinearMap.toMatrix_one]
  map_add' x y := by
    dsimp only  -- porting node: needed due to new-style structures
    rw [AlgHom.map_add, LinearEquiv.map_add]
  map_mul' x y := by
    dsimp only  -- porting node: needed due to new-style structures
    rw [AlgHom.map_mul, LinearMap.toMatrix_mul]
  commutes' r := by
    dsimp only  -- porting node: needed due to new-style structures
    ext
    rw [lmul_algebraMap, toMatrix_lsmul, algebraMap_eq_diagonal, Pi.algebraMap_def,
      Algebra.id.map_eq_self]
#align algebra.left_mul_matrix Algebra.leftMulMatrix

def algEquivMatrix' [Fintype n] : Module.End R (n → R) ≃ₐ[R] Matrix n n R :=
  { LinearMap.toMatrix' with
    map_mul' := LinearMap.toMatrix'_comp
    commutes' := LinearMap.toMatrix'_algebraMap }
#align alg_equiv_matrix' algEquivMatrix'

def LinearEquiv.algConj (e : M₁ ≃ₗ[R] M₂) : Module.End R M₁ ≃ₐ[R] Module.End R M₂ :=
  { e.conj with
    map_mul' := fun f g ↦ by apply e.arrowCongr_comp
    commutes' := fun r ↦ by
      change e.conj (r • LinearMap.id) = r • LinearMap.id
      rw [LinearEquiv.map_smul, LinearEquiv.conj_id] }
#align linear_equiv.alg_conj LinearEquiv.algConj

def algEquivMatrix [Fintype n] (h : Basis n R M) : Module.End R M ≃ₐ[R] Matrix n n R :=
  h.equivFun.algConj.trans algEquivMatrix'
#align alg_equiv_matrix algEquivMatrix