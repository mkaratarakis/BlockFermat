def SameRay (v₁ v₂ : M) : Prop :=
  v₁ = 0 ∨ v₂ = 0 ∨ ∃ r₁ r₂ : R, 0 < r₁ ∧ 0 < r₂ ∧ r₁ • v₁ = r₂ • v₂
#align same_ray SameRay

def RayVector (R M : Type*) [Zero M] :=
  { v : M // v ≠ 0 }
#align ray_vector RayVector

def Module.Ray :=
  Quotient (RayVector.Setoid R M)
#align module.ray Module.Ray

def rayOfNeZero (v : M) (h : v ≠ 0) : Module.Ray R M :=
  ⟦⟨v, h⟩⟧
#align ray_of_ne_zero rayOfNeZero

def RayVector.mapLinearEquiv (e : M ≃ₗ[R] N) : RayVector R M ≃ RayVector R N :=
  Equiv.subtypeEquiv e.toEquiv fun _ => e.map_ne_zero_iff.symm
#align ray_vector.map_linear_equiv RayVector.mapLinearEquiv

def Module.Ray.map (e : M ≃ₗ[R] N) : Module.Ray R M ≃ Module.Ray R N :=
  Quotient.congr (RayVector.mapLinearEquiv e) fun _ _=> (SameRay.sameRay_map_iff _).symm
#align module.ray.map Module.Ray.map

def someRayVector (x : Module.Ray R M) : RayVector R M :=
  Quotient.out x
#align module.ray.some_ray_vector Module.Ray.someRayVector

def someVector (x : Module.Ray R M) : M :=
  x.someRayVector
#align module.ray.some_vector Module.Ray.someVector