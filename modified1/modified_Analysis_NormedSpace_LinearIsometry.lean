def Simps.apply (σ₁₂ : R →+* R₂) (E E₂ : Type*) [SeminormedAddCommGroup E]
    [SeminormedAddCommGroup E₂] [Module R E] [Module R₂ E₂] (h : E →ₛₗᵢ[σ₁₂] E₂) : E → E₂ :=
  h
#align linear_isometry.simps.apply LinearIsometry.Simps.apply

def toContinuousLinearMap : E →SL[σ₁₂] E₂ :=
  ⟨f.toLinearMap, f.continuous⟩
#align linear_isometry.to_continuous_linear_map LinearIsometry.toContinuousLinearMap

def id : E →ₗᵢ[R] E :=
  ⟨LinearMap.id, fun _ => rfl⟩
#align linear_isometry.id LinearIsometry.id

def comp (g : E₂ →ₛₗᵢ[σ₂₃] E₃) (f : E →ₛₗᵢ[σ₁₂] E₂) : E →ₛₗᵢ[σ₁₃] E₃ :=
  ⟨g.toLinearMap.comp f.toLinearMap, fun _ => (norm_map g _).trans (norm_map f _)⟩
#align linear_isometry.comp LinearIsometry.comp

def : (1 : E →ₗᵢ[R] E) = id :=
  rfl
#align linear_isometry.one_def LinearIsometry.one_def

def (f g : E →ₗᵢ[R] E) : (f * g : E →ₗᵢ[R] E) = f.comp g :=
  rfl
#align linear_isometry.mul_def LinearIsometry.mul_def

def LinearMap.toLinearIsometry (f : E →ₛₗ[σ₁₂] E₂) (hf : Isometry f) : E →ₛₗᵢ[σ₁₂] E₂ :=
  { f with
    norm_map' := by
      simp_rw [← dist_zero_right]
      simpa using (hf.dist_eq · 0) }
#align linear_map.to_linear_isometry LinearMap.toLinearIsometry

def subtypeₗᵢ : p →ₗᵢ[R'] E :=
  ⟨p.subtype, fun _ => rfl⟩
#align submodule.subtypeₗᵢ Submodule.subtypeₗᵢ

def ofBounds (e : E ≃ₛₗ[σ₁₂] E₂) (h₁ : ∀ x, ‖e x‖ ≤ ‖x‖) (h₂ : ∀ y, ‖e.symm y‖ ≤ ‖y‖) :
    E ≃ₛₗᵢ[σ₁₂] E₂ :=
  ⟨e, fun x => le_antisymm (h₁ x) <| by simpa only [e.symm_apply_apply] using h₂ (e x)⟩
#align linear_isometry_equiv.of_bounds LinearIsometryEquiv.ofBounds

def toLinearIsometry : E →ₛₗᵢ[σ₁₂] E₂ :=
  ⟨e.1, e.2⟩
#align linear_isometry_equiv.to_linear_isometry LinearIsometryEquiv.toLinearIsometry

def toIsometryEquiv : E ≃ᵢ E₂ :=
  ⟨e.toLinearEquiv.toEquiv, e.isometry⟩
#align linear_isometry_equiv.to_isometry_equiv LinearIsometryEquiv.toIsometryEquiv

def toHomeomorph : E ≃ₜ E₂ :=
  e.toIsometryEquiv.toHomeomorph
#align linear_isometry_equiv.to_homeomorph LinearIsometryEquiv.toHomeomorph

def toContinuousLinearEquiv : E ≃SL[σ₁₂] E₂ :=
  { e.toLinearIsometry.toContinuousLinearMap, e.toHomeomorph with }
#align linear_isometry_equiv.to_continuous_linear_equiv LinearIsometryEquiv.toContinuousLinearEquiv

def refl : E ≃ₗᵢ[R] E :=
  ⟨LinearEquiv.refl R E, fun _ => rfl⟩
#align linear_isometry_equiv.refl LinearIsometryEquiv.refl

def ulift : ULift E ≃ₗᵢ[R] E :=
  { ContinuousLinearEquiv.ulift with norm_map' := fun _ => rfl }
#align linear_isometry_equiv.ulift LinearIsometryEquiv.ulift

def symm : E₂ ≃ₛₗᵢ[σ₂₁] E :=
  ⟨e.toLinearEquiv.symm, fun x =>
    (e.norm_map _).symm.trans <| congr_arg norm <| e.toLinearEquiv.apply_symm_apply x⟩
#align linear_isometry_equiv.symm LinearIsometryEquiv.symm

def Simps.apply (σ₁₂ : R →+* R₂) {σ₂₁ : R₂ →+* R} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
    (E E₂ : Type*) [SeminormedAddCommGroup E] [SeminormedAddCommGroup E₂] [Module R E]
    [Module R₂ E₂] (h : E ≃ₛₗᵢ[σ₁₂] E₂) : E → E₂ :=
  h
#align linear_isometry_equiv.simps.apply LinearIsometryEquiv.Simps.apply

def Simps.symm_apply (σ₁₂ : R →+* R₂) {σ₂₁ : R₂ →+* R} [RingHomInvPair σ₁₂ σ₂₁]
    [RingHomInvPair σ₂₁ σ₁₂] (E E₂ : Type*) [SeminormedAddCommGroup E] [SeminormedAddCommGroup E₂]
    [Module R E] [Module R₂ E₂] (h : E ≃ₛₗᵢ[σ₁₂] E₂) : E₂ → E :=
  h.symm
#align linear_isometry_equiv.simps.symm_apply LinearIsometryEquiv.Simps.symm_apply

def trans (e' : E₂ ≃ₛₗᵢ[σ₂₃] E₃) : E ≃ₛₗᵢ[σ₁₃] E₃ :=
  ⟨e.toLinearEquiv.trans e'.toLinearEquiv, fun _ => (e'.norm_map _).trans (e.norm_map _)⟩
#align linear_isometry_equiv.trans LinearIsometryEquiv.trans

def : (1 : E ≃ₗᵢ[R] E) = refl _ _ :=
  rfl
#align linear_isometry_equiv.one_def LinearIsometryEquiv.one_def

def (e e' : E ≃ₗᵢ[R] E) : (e * e' : E ≃ₗᵢ[R] E) = e'.trans e :=
  rfl
#align linear_isometry_equiv.mul_def LinearIsometryEquiv.mul_def

def (e : E ≃ₗᵢ[R] E) : (e⁻¹ : E ≃ₗᵢ[R] E) = e.symm :=
  rfl
#align linear_isometry_equiv.inv_def LinearIsometryEquiv.inv_def

def ofSurjective (f : F →ₛₗᵢ[σ₁₂] E₂) (hfr : Function.Surjective f) :
    F ≃ₛₗᵢ[σ₁₂] E₂ :=
  { LinearEquiv.ofBijective f.toLinearMap ⟨f.injective, hfr⟩ with norm_map' := f.norm_map }
#align linear_isometry_equiv.of_surjective LinearIsometryEquiv.ofSurjective

def ofLinearIsometry (f : E →ₛₗᵢ[σ₁₂] E₂) (g : E₂ →ₛₗ[σ₂₁] E)
    (h₁ : f.toLinearMap.comp g = LinearMap.id) (h₂ : g.comp f.toLinearMap = LinearMap.id) :
    E ≃ₛₗᵢ[σ₁₂] E₂ :=
  { LinearEquiv.ofLinear f.toLinearMap g h₁ h₂ with norm_map' := fun x => f.norm_map x }
#align linear_isometry_equiv.of_linear_isometry LinearIsometryEquiv.ofLinearIsometry

def neg : E ≃ₗᵢ[R] E :=
  { LinearEquiv.neg R with norm_map' := norm_neg }
#align linear_isometry_equiv.neg LinearIsometryEquiv.neg

def prodAssoc [Module R E₂] [Module R E₃] : (E × E₂) × E₃ ≃ₗᵢ[R] E × E₂ × E₃ :=
  { Equiv.prodAssoc E E₂ E₃ with
    toFun := Equiv.prodAssoc E E₂ E₃
    invFun := (Equiv.prodAssoc E E₂ E₃).symm
    map_add' := by simp [-_root_.map_add] --  Fix timeout from #8386

def ofTop {R : Type*} [Ring R] [Module R E] (p : Submodule R E) (hp : p = ⊤) : p ≃ₗᵢ[R] E :=
  { p.subtypeₗᵢ with toLinearEquiv := LinearEquiv.ofTop p hp }
#align linear_isometry_equiv.of_top LinearIsometryEquiv.ofTop

def ofEq (hpq : p = q) : p ≃ₗᵢ[R'] q :=
  { LinearEquiv.ofEq p q hpq with norm_map' := fun _ => rfl }
#align linear_isometry_equiv.of_eq LinearIsometryEquiv.ofEq

def LinearIsometry.equivRange {R S : Type*} [Semiring R] [Ring S] [Module S E]
    [Module R F] {σ₁₂ : R →+* S} {σ₂₁ : S →+* R} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
    (f : F →ₛₗᵢ[σ₁₂] E) : F ≃ₛₗᵢ[σ₁₂] (LinearMap.range f.toLinearMap) :=
  { f with toLinearEquiv := LinearEquiv.ofInjective f.toLinearMap f.injective }
#align linear_isometry.equiv_range LinearIsometry.equivRange

structure LinearIsometry (σ₁₂ : R →+* R₂) (E E₂ : Type*) [SeminormedAddCommGroup E]
  [SeminormedAddCommGroup E₂] [Module R E] [Module R₂ E₂] extends E →ₛₗ[σ₁₂] E₂ where
  norm_map' : ∀ x, ‖toLinearMap x‖ = ‖x‖
#align linear_isometry LinearIsometry

structure LinearIsometryEquiv (σ₁₂ : R →+* R₂) {σ₂₁ : R₂ →+* R} [RingHomInvPair σ₁₂ σ₂₁]
  [RingHomInvPair σ₂₁ σ₁₂] (E E₂ : Type*) [SeminormedAddCommGroup E] [SeminormedAddCommGroup E₂]
  [Module R E] [Module R₂ E₂] extends E ≃ₛₗ[σ₁₂] E₂ where
  norm_map' : ∀ x, ‖toLinearEquiv x‖ = ‖x‖
#align linear_isometry_equiv LinearIsometryEquiv

structure with definitions. Because we have multiple ways to
express `LinearIsometryEquiv.refl`, `LinearIsometryEquiv.symm`, and
`LinearIsometryEquiv.trans`, we want simp lemmas for every combination.
The assumption made here is that if you're using the group structure, you want to preserve it
after simp.

This copies the approach used by the lemmas near `Equiv.Perm.trans_one`. -/


@[simp]
theorem trans_one : e.trans (1 : E₂ ≃ₗᵢ[R₂] E₂) = e :=
  trans_refl _
#align linear_isometry_equiv.trans_one LinearIsometryEquiv.trans_one