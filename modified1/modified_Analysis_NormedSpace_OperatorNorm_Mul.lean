def mul : 𝕜' →L[𝕜] 𝕜' →L[𝕜] 𝕜' :=
  (LinearMap.mul 𝕜 𝕜').mkContinuous₂ 1 fun x y => by simpa using norm_mul_le x y
#align continuous_linear_map.mul ContinuousLinearMap.mul

def _root_.NonUnitalAlgHom.Lmul : 𝕜' →ₙₐ[𝕜] 𝕜' →L[𝕜] 𝕜' :=
  { mul 𝕜 𝕜' with
    map_mul' := fun _ _ ↦ ext fun _ ↦ mul_assoc _ _ _
    map_zero' := ext fun _ ↦ zero_mul _ }

variable {𝕜 𝕜'} in
@[simp]
theorem _root_.NonUnitalAlgHom.coe_Lmul : ⇑(NonUnitalAlgHom.Lmul 𝕜 𝕜') = mul 𝕜 𝕜' :=
  rfl

/-- Simultaneous left- and right-multiplication in a non-unital normed algebra, considered as a
continuous trilinear map. This is akin to its non-continuous version `LinearMap.mulLeftRight`,
but there is a minor difference: `LinearMap.mulLeftRight` is uncurried. -/
def mulLeftRight : 𝕜' →L[𝕜] 𝕜' →L[𝕜] 𝕜' →L[𝕜] 𝕜' :=
  ((compL 𝕜 𝕜' 𝕜' 𝕜').comp (mul 𝕜 𝕜').flip).flip.comp (mul 𝕜 𝕜')
#align continuous_linear_map.mul_left_right ContinuousLinearMap.mulLeftRight

def mulₗᵢ : 𝕜' →ₗᵢ[𝕜] 𝕜' →L[𝕜] 𝕜' where
  toLinearMap := mul 𝕜 𝕜'
  norm_map' x := opNorm_mul_apply 𝕜 𝕜' x
#align continuous_linear_map.mulₗᵢ ContinuousLinearMap.mulₗᵢₓ

def ring_lmap_equiv_selfₗ : (𝕜 →L[𝕜] E) ≃ₗ[𝕜] E where
  toFun := fun f ↦ f 1
  invFun := (ContinuousLinearMap.id 𝕜 𝕜).smulRight
  map_smul' := fun a f ↦ by simp only [coe_smul', Pi.smul_apply, RingHom.id_apply]
  map_add' := fun f g ↦ by simp only [add_apply]
  left_inv := fun f ↦ by ext; simp only [smulRight_apply, coe_id', id.def, one_smul]
  right_inv := fun m ↦ by simp only [smulRight_apply, id_apply, one_smul]

/-- If `M` is a normed space over `𝕜`, then the space of maps `𝕜 →L[𝕜] M` is linearly isometrically
equivalent to `M`. -/
def ring_lmap_equiv_self : (𝕜 →L[𝕜] E) ≃ₗᵢ[𝕜] E where
  toLinearEquiv := ring_lmap_equiv_selfₗ 𝕜 E
  norm_map' := by
    refine fun f ↦ le_antisymm ?_ ?_
    · simpa only [norm_one, mul_one] using le_opNorm f 1
    · refine opNorm_le_bound' f (norm_nonneg <| f 1) (fun x _ ↦ ?_)
      rw [(by rw [smul_eq_mul, mul_one] : f x = f (x • 1)), ContinuousLinearMap.map_smul,
        norm_smul, mul_comm, (by rfl : ring_lmap_equiv_selfₗ 𝕜 E f = f 1)]

end RingEquiv

end MultiplicationLinear

section SMulLinear

variable (𝕜) (𝕜' : Type*) [NormedField 𝕜']
variable [NormedAlgebra 𝕜 𝕜'] [NormedSpace 𝕜' E] [IsScalarTower 𝕜 𝕜' E]

/-- Scalar multiplication as a continuous bilinear map. -/
def lsmul : 𝕜' →L[𝕜] E →L[𝕜] E :=
  ((Algebra.lsmul 𝕜 𝕜 E).toLinearMap : 𝕜' →ₗ[𝕜] E →ₗ[𝕜] E).mkContinuous₂ 1 fun c x => by
    simpa only [one_mul] using norm_smul_le c x
#align continuous_linear_map.lsmul ContinuousLinearMap.lsmul

structure than `ContinuousLinearMap.mul`, but there is no longer continuity
bundled in the first coordinate.  An alternative viewpoint is that this upgrades
`NonUnitalAlgHom.lmul` from a homomorphism into linear maps to a homomorphism into *continuous*
linear maps. -/
def _root_.NonUnitalAlgHom.Lmul : 𝕜' →ₙₐ[𝕜] 𝕜' →L[𝕜] 𝕜' :=
  { mul 𝕜 𝕜' with
    map_mul' := fun _ _ ↦ ext fun _ ↦ mul_assoc _ _ _
    map_zero' := ext fun _ ↦ zero_mul _ }

variable {𝕜 𝕜'} in
@[simp]
theorem _root_.NonUnitalAlgHom.coe_Lmul : ⇑(NonUnitalAlgHom.Lmul 𝕜 𝕜') = mul 𝕜 𝕜' :=
  rfl

/-- Simultaneous left- and right-multiplication in a non-unital normed algebra, considered as a
continuous trilinear map. This is akin to its non-continuous version `LinearMap.mulLeftRight`,
but there is a minor difference: `LinearMap.mulLeftRight` is uncurried. -/
def mulLeftRight : 𝕜' →L[𝕜] 𝕜' →L[𝕜] 𝕜' →L[𝕜] 𝕜' :=
  ((compL 𝕜 𝕜' 𝕜' 𝕜').comp (mul 𝕜 𝕜').flip).flip.comp (mul 𝕜 𝕜')
#align continuous_linear_map.mul_left_right ContinuousLinearMap.mulLeftRight