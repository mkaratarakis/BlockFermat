def inclusionInDoubleDual : E →L[𝕜] Dual 𝕜 (Dual 𝕜 E) :=
  ContinuousLinearMap.apply 𝕜 𝕜
#align normed_space.inclusion_in_double_dual NormedSpace.inclusionInDoubleDual

def (x : E) (f : Dual 𝕜 E) : inclusionInDoubleDual 𝕜 E x f = f x :=
  rfl
#align normed_space.dual_def NormedSpace.dual_def

def dualPairing : Dual 𝕜 E →ₗ[𝕜] E →ₗ[𝕜] 𝕜 :=
  ContinuousLinearMap.coeLM 𝕜
#align normed_space.dual_pairing NormedSpace.dualPairing

def inclusionInDoubleDualLi : E →ₗᵢ[𝕜] Dual 𝕜 (Dual 𝕜 E) :=
  { inclusionInDoubleDual 𝕜 E with
    norm_map' := by
      intro x
      apply le_antisymm
      · exact double_dual_bound 𝕜 E x
      rw [ContinuousLinearMap.norm_def]
      refine' le_csInf ContinuousLinearMap.bounds_nonempty _
      rintro c ⟨hc1, hc2⟩
      exact norm_le_dual_bound 𝕜 x hc1 hc2 }
#align normed_space.inclusion_in_double_dual_li NormedSpace.inclusionInDoubleDualLi

def polar (𝕜 : Type*) [NontriviallyNormedField 𝕜] {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace 𝕜 E] : Set E → Set (Dual 𝕜 E) :=
  (dualPairing 𝕜 E).flip.polar
#align normed_space.polar NormedSpace.polar