def toLinearIsometryEquiv (li : E₁ →ₗᵢ[R₁] F) (h : finrank R₁ E₁ = finrank R₁ F) :
    E₁ ≃ₗᵢ[R₁] F where
  toLinearEquiv := li.toLinearMap.linearEquivOfInjective li.injective h
  norm_map' := li.norm_map'
#align linear_isometry.to_linear_isometry_equiv LinearIsometry.toLinearIsometryEquiv

def toAffineIsometryEquiv [Inhabited P₁] (li : P₁ →ᵃⁱ[𝕜] P₂) (h : finrank 𝕜 V₁ = finrank 𝕜 V₂) :
    P₁ ≃ᵃⁱ[𝕜] P₂ :=
  AffineIsometryEquiv.mk' li (li.linearIsometry.toLinearIsometryEquiv h)
    (Inhabited.default (α := P₁)) fun p => by simp
#align affine_isometry.to_affine_isometry_equiv AffineIsometry.toAffineIsometryEquiv

def AffineEquiv.toHomeomorphOfFiniteDimensional (f : PE ≃ᵃ[𝕜] PF) : PE ≃ₜ PF where
  toEquiv := f.toEquiv
  continuous_toFun := f.continuous_of_finiteDimensional
  continuous_invFun :=
    haveI : FiniteDimensional 𝕜 F := f.linear.finiteDimensional
    f.symm.continuous_of_finiteDimensional
#align affine_equiv.to_homeomorph_of_finite_dimensional AffineEquiv.toHomeomorphOfFiniteDimensional

def lipschitzExtensionConstant (E' : Type*) [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [FiniteDimensional ℝ E'] : ℝ≥0 :=
  let A := (Basis.ofVectorSpace ℝ E').equivFun.toContinuousLinearEquiv
  max (‖A.symm.toContinuousLinearMap‖₊ * ‖A.toContinuousLinearMap‖₊) 1
#align lipschitz_extension_constant lipschitzExtensionConstant

def ContinuousLinearEquiv.piRing (ι : Type*) [Fintype ι] [DecidableEq ι] :
    ((ι → 𝕜) →L[𝕜] E) ≃L[𝕜] ι → E :=
  { LinearMap.toContinuousLinearMap.symm.trans (LinearEquiv.piRing 𝕜 E ι 𝕜) with
    continuous_toFun := by
      refine' continuous_pi fun i => _
      exact (ContinuousLinearMap.apply 𝕜 E (Pi.single i 1)).continuous
    continuous_invFun := by
      simp_rw [LinearEquiv.invFun_eq_symm, LinearEquiv.trans_symm, LinearEquiv.symm_symm]
      -- Note: added explicit type and removed `change` that tried to achieve the same
      refine AddMonoidHomClass.continuous_of_bound
        (LinearMap.toContinuousLinearMap.toLinearMap.comp
            (LinearEquiv.piRing 𝕜 E ι 𝕜).symm.toLinearMap)
        (Fintype.card ι : ℝ) fun g => ?_
      rw [← nsmul_eq_mul]
      refine opNorm_le_bound _ (nsmul_nonneg (norm_nonneg g) (Fintype.card ι)) fun t => ?_
      simp_rw [LinearMap.coe_comp, LinearEquiv.coe_toLinearMap, Function.comp_apply,
        LinearMap.coe_toContinuousLinearMap', LinearEquiv.piRing_symm_apply]
      apply le_trans (norm_sum_le _ _)
      rw [smul_mul_assoc]
      refine' Finset.sum_le_card_nsmul _ _ _ fun i _ => _
      rw [norm_smul, mul_comm]
      gcongr <;> apply norm_le_pi_norm }
#align continuous_linear_equiv.pi_ring ContinuousLinearEquiv.piRing