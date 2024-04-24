def toContinuousLinearMap : (E →ₗ[𝕜] F') ≃ₗ[𝕜] E →L[𝕜] F' where
  toFun f := ⟨f, f.continuous_of_finiteDimensional⟩
  invFun := (↑)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := ContinuousLinearMap.coe_injective rfl
#align linear_map.to_continuous_linear_map LinearMap.toContinuousLinearMap

def toContinuousLinearEquiv (e : E ≃ₗ[𝕜] F) : E ≃L[𝕜] F :=
  { e with
    continuous_toFun := e.toLinearMap.continuous_of_finiteDimensional
    continuous_invFun :=
      haveI : FiniteDimensional 𝕜 F := e.finiteDimensional
      e.symm.toLinearMap.continuous_of_finiteDimensional }
#align linear_equiv.to_continuous_linear_equiv LinearEquiv.toContinuousLinearEquiv

def ContinuousLinearEquiv.ofFinrankEq (cond : finrank 𝕜 E = finrank 𝕜 F) : E ≃L[𝕜] F :=
  (LinearEquiv.ofFinrankEq E F cond).toContinuousLinearEquiv
#align continuous_linear_equiv.of_finrank_eq ContinuousLinearEquiv.ofFinrankEq

def constrL (v : Basis ι 𝕜 E) (f : ι → F) : E →L[𝕜] F :=
  haveI : FiniteDimensional 𝕜 E := FiniteDimensional.of_fintype_basis v
  LinearMap.toContinuousLinearMap (v.constr 𝕜 f)
#align basis.constrL Basis.constrL

def equivFunL (v : Basis ι 𝕜 E) : E ≃L[𝕜] ι → 𝕜 :=
  { v.equivFun with
    continuous_toFun :=
      haveI : FiniteDimensional 𝕜 E := FiniteDimensional.of_fintype_basis v
      v.equivFun.toLinearMap.continuous_of_finiteDimensional
    continuous_invFun := by
      change Continuous v.equivFun.symm.toFun
      exact v.equivFun.symm.toLinearMap.continuous_of_finiteDimensional }
#align basis.equiv_funL Basis.equivFunL

def toContinuousLinearEquivOfDetNeZero (f : E →L[𝕜] E) (hf : f.det ≠ 0) : E ≃L[𝕜] E :=
  ((f : E →ₗ[𝕜] E).equivOfDetNeZero hf).toContinuousLinearEquiv
#align continuous_linear_map.to_continuous_linear_equiv_of_det_ne_zero ContinuousLinearMap.toContinuousLinearEquivOfDetNeZero