def UniformConvergenceCLM [TopologicalSpace F] [TopologicalAddGroup F] (_ : Set (Set E)) :=
  E →SL[σ] F

namespace UniformConvergenceCLM

instance instFunLike [TopologicalSpace F] [TopologicalAddGroup F]
    (𝔖 : Set (Set E)) : FunLike (UniformConvergenceCLM σ F 𝔖) E F :=
  ContinuousLinearMap.funLike

instance instContinuousSemilinearMapClass [TopologicalSpace F] [TopologicalAddGroup F]
    (𝔖 : Set (Set E)) : ContinuousSemilinearMapClass (UniformConvergenceCLM σ F 𝔖) σ E F :=
  ContinuousLinearMap.continuousSemilinearMapClass

instance instTopologicalSpace [TopologicalSpace F] [TopologicalAddGroup F] (𝔖 : Set (Set E)) :
    TopologicalSpace (UniformConvergenceCLM σ F 𝔖) :=
  (@UniformOnFun.topologicalSpace E F (TopologicalAddGroup.toUniformSpace F) 𝔖).induced
    (DFunLike.coe : (UniformConvergenceCLM σ F 𝔖) → (E →ᵤ[𝔖] F))
#align continuous_linear_map.strong_topology UniformConvergenceCLM.instTopologicalSpace

def precomp [TopologicalAddGroup G] [ContinuousConstSMul 𝕜₃ G] [RingHomSurjective σ]
    [RingHomIsometric σ] (L : E →SL[σ] F) : (F →SL[τ] G) →L[𝕜₃] E →SL[ρ] G
    where
  toFun f := f.comp L
  map_add' f g := add_comp f g L
  map_smul' a f := smul_comp a f L
  cont := by
    letI : UniformSpace G := TopologicalAddGroup.toUniformSpace G
    haveI : UniformAddGroup G := comm_topologicalAddGroup_is_uniform
    rw [(UniformConvergenceCLM.embedding_coeFn _ _ _).continuous_iff]
    -- Porting note: without this, the following doesn't work
    change Continuous ((fun f ↦ UniformOnFun.ofFun _ (f ∘ L)) ∘ DFunLike.coe)
    exact (UniformOnFun.precomp_uniformContinuous fun S hS => hS.image L).continuous.comp
        (UniformConvergenceCLM.embedding_coeFn _ _ _).continuous
#align continuous_linear_map.precomp ContinuousLinearMap.precomp

def postcomp [TopologicalAddGroup F] [TopologicalAddGroup G] [ContinuousConstSMul 𝕜₃ G]
    [ContinuousConstSMul 𝕜₂ F] (L : F →SL[τ] G) : (E →SL[σ] F) →SL[τ] E →SL[ρ] G
    where
  toFun f := L.comp f
  map_add' := comp_add L
  map_smul' := comp_smulₛₗ L
  cont := by
    letI : UniformSpace G := TopologicalAddGroup.toUniformSpace G
    haveI : UniformAddGroup G := comm_topologicalAddGroup_is_uniform
    letI : UniformSpace F := TopologicalAddGroup.toUniformSpace F
    haveI : UniformAddGroup F := comm_topologicalAddGroup_is_uniform
    rw [(UniformConvergenceCLM.embedding_coeFn _ _ _).continuous_iff]
    exact
      (UniformOnFun.postcomp_uniformContinuous L.uniformContinuous).continuous.comp
        (UniformConvergenceCLM.embedding_coeFn _ _ _).continuous
#align continuous_linear_map.postcomp ContinuousLinearMap.postcomp

def toLinearMap₂ (L : E →L[𝕜] F →L[𝕜] G) : E →ₗ[𝕜] F →ₗ[𝕜] G := (coeLM 𝕜).comp L.toLinearMap

@[simp] lemma toLinearMap₂_apply (L : E →L[𝕜] F →L[𝕜] G) (v : E) (w : F) :
    L.toLinearMap₂ v w = L v w := rfl

end BilinearMaps

end ContinuousLinearMap

open ContinuousLinearMap

namespace ContinuousLinearEquiv

/-! ### Continuous linear equivalences -/

def arrowCongrSL (e₁₂ : E ≃SL[σ₁₂] F) (e₄₃ : H ≃SL[σ₄₃] G) :
    (E →SL[σ₁₄] H) ≃SL[σ₄₃] F →SL[σ₂₃] G :=
{ e₁₂.arrowCongrEquiv e₄₃ with
    -- given explicitly to help `simps`
    toFun := fun L => (e₄₃ : H →SL[σ₄₃] G).comp (L.comp (e₁₂.symm : F →SL[σ₂₁] E))
    -- given explicitly to help `simps`
    invFun := fun L => (e₄₃.symm : G →SL[σ₃₄] H).comp (L.comp (e₁₂ : E →SL[σ₁₂] F))
    map_add' := fun f g => by simp only [add_comp, comp_add]
    map_smul' := fun t f => by simp only [smul_comp, comp_smulₛₗ]
    continuous_toFun := ((postcomp F e₄₃.toContinuousLinearMap).comp
      (precomp H e₁₂.symm.toContinuousLinearMap)).continuous
    continuous_invFun := ((precomp H e₁₂.toContinuousLinearMap).comp
      (postcomp F e₄₃.symm.toContinuousLinearMap)).continuous }
set_option linter.uppercaseLean3 false in
#align continuous_linear_equiv.arrow_congrSL ContinuousLinearEquiv.arrowCongrSL

def arrowCongr (e₁ : E ≃L[𝕜] F) (e₂ : H ≃L[𝕜] G) : (E →L[𝕜] H) ≃L[𝕜] F →L[𝕜] G :=
  e₁.arrowCongrSL e₂
#align continuous_linear_equiv.arrow_congr ContinuousLinearEquiv.arrowCongr

structure associated with `ContinuousLinearMap.strongTopology`. We make sure
that this has nice definitional properties. -/
instance instUniformSpace [UniformSpace F] [UniformAddGroup F]
    (𝔖 : Set (Set E)) : UniformSpace (UniformConvergenceCLM σ F 𝔖) :=
  UniformSpace.replaceTopology
    ((UniformOnFun.uniformSpace E F 𝔖).comap
      (DFunLike.coe : (UniformConvergenceCLM σ F 𝔖) → (E →ᵤ[𝔖] F)))
    (by rw [UniformConvergenceCLM.instTopologicalSpace, UniformAddGroup.toUniformSpace_eq]; rfl)
#align continuous_linear_map.strong_uniformity UniformConvergenceCLM.instUniformSpace