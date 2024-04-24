def rotation : circle →* ℂ ≃ₗᵢ[ℝ] ℂ where
  toFun a :=
    { DistribMulAction.toLinearEquiv ℝ ℂ a with
      norm_map' := fun x => show |a * x| = |x| by rw [map_mul, abs_coe_circle, one_mul] }
  map_one' := LinearIsometryEquiv.ext <| one_smul circle
  map_mul' a b := LinearIsometryEquiv.ext <| mul_smul a b
#align rotation rotation

def rotationOf (e : ℂ ≃ₗᵢ[ℝ] ℂ) : circle :=
  ⟨e 1 / Complex.abs (e 1), by simp⟩
#align rotation_of rotationOf