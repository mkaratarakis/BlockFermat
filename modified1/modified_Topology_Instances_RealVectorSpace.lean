def toRealLinearMap (f : E →+ F) (hf : Continuous f) : E →L[ℝ] F :=
  ⟨{  toFun := f
      map_add' := f.map_add
      map_smul' := map_real_smul f hf }, hf⟩
#align add_monoid_hom.to_real_linear_map AddMonoidHom.toRealLinearMap

def AddEquiv.toRealLinearEquiv (e : E ≃+ F) (h₁ : Continuous e) (h₂ : Continuous e.symm) :
    E ≃L[ℝ] F :=
  { e, e.toAddMonoidHom.toRealLinearMap h₁ with }
#align add_equiv.to_real_linear_equiv AddEquiv.toRealLinearEquiv

structure of a topological `ℝ`-module, so for any
topological `ℝ`-algebra `A` (e.g. `A = ℂ`) and any topological group that is both a topological
`ℝ`-module and a topological `A`-module, these structures agree. -/
instance (priority := 900) Real.isScalarTower [T2Space E] {A : Type*} [TopologicalSpace A] [Ring A]
    [Algebra ℝ A] [Module A E] [ContinuousSMul ℝ A] [ContinuousSMul A E] : IsScalarTower ℝ A E :=
  ⟨fun r x y => map_real_smul ((smulAddHom A E).flip y) (continuous_id.smul continuous_const) r x⟩
#align real.is_scalar_tower Real.isScalarTower