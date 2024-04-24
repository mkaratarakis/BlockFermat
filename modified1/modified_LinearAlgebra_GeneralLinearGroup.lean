def GeneralLinearGroup :=
  (M →ₗ[R] M)ˣ
#align linear_map.general_linear_group LinearMap.GeneralLinearGroup

def toLinearEquiv (f : GeneralLinearGroup R M) : M ≃ₗ[R] M :=
  { f.val with
    invFun := f.inv.toFun
    left_inv := fun m ↦ show (f.inv * f.val) m = m by erw [f.inv_val]; simp
    right_inv := fun m ↦ show (f.val * f.inv) m = m by erw [f.val_inv]; simp }
#align linear_map.general_linear_group.to_linear_equiv LinearMap.GeneralLinearGroup.toLinearEquiv

def ofLinearEquiv (f : M ≃ₗ[R] M) : GeneralLinearGroup R M where
  val := f
  inv := (f.symm : M →ₗ[R] M)
  val_inv := LinearMap.ext fun _ ↦ f.apply_symm_apply _
  inv_val := LinearMap.ext fun _ ↦ f.symm_apply_apply _
#align linear_map.general_linear_group.of_linear_equiv LinearMap.GeneralLinearGroup.ofLinearEquiv

def generalLinearEquiv : GeneralLinearGroup R M ≃* M ≃ₗ[R] M where
  toFun := toLinearEquiv
  invFun := ofLinearEquiv
  left_inv f := by ext; rfl
  right_inv f := by ext; rfl
  map_mul' x y := by ext; rfl
#align linear_map.general_linear_group.general_linear_equiv LinearMap.GeneralLinearGroup.generalLinearEquiv