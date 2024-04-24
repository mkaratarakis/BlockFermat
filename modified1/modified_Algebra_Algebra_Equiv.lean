def toAlgEquiv {F R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A]
    [Algebra R B] [EquivLike F A B] [AlgEquivClass F R A B] (f : F) : A ≃ₐ[R] B :=
  { (f : A ≃ B), (f : A ≃+* B) with commutes' := commutes f }

instance (F R A B : Type*) [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
    [EquivLike F A B] [AlgEquivClass F R A B] : CoeTC F (A ≃ₐ[R] B) :=
  ⟨toAlgEquiv⟩
end AlgEquivClass

namespace AlgEquiv

universe uR uA₁ uA₂ uA₃ uA₁' uA₂' uA₃'
variable {R : Type uR}
variable {A₁ : Type uA₁} {A₂ : Type uA₂} {A₃ : Type uA₃}
variable {A₁' : Type uA₁'} {A₂' : Type uA₂'} {A₃' : Type uA₃'}

section Semiring

variable [CommSemiring R] [Semiring A₁] [Semiring A₂] [Semiring A₃]
variable [Semiring A₁'] [Semiring A₂'] [Semiring A₃']
variable [Algebra R A₁] [Algebra R A₂] [Algebra R A₃]
variable [Algebra R A₁'] [Algebra R A₂'] [Algebra R A₃']
variable (e : A₁ ≃ₐ[R] A₂)

instance : EquivLike (A₁ ≃ₐ[R] A₂) A₁ A₂ where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by
    obtain ⟨⟨f,_⟩,_⟩ := f
    obtain ⟨⟨g,_⟩,_⟩ := g
    congr

/-- Helper instance since the coercion is not always found. -/
instance : FunLike (A₁ ≃ₐ[R] A₂) A₁ A₂ where
  coe := DFunLike.coe
  coe_injective' := DFunLike.coe_injective'

instance : AlgEquivClass (A₁ ≃ₐ[R] A₂) R A₁ A₂ where
  map_add f := f.map_add'
  map_mul f := f.map_mul'
  commutes f := f.commutes'

-- Porting note: the default simps projection was `e.toEquiv.toFun`, it should be `FunLike.coe`
/-- See Note [custom simps projection] -/
def Simps.apply (e : A₁ ≃ₐ[R] A₂) : A₁ → A₂ :=
  e

-- Porting note: the default simps projection was `e.toEquiv`, it should be `EquivLike.toEquiv`
/-- See Note [custom simps projection] -/
def Simps.toEquiv (e : A₁ ≃ₐ[R] A₂) : A₁ ≃ A₂ :=
  e

-- Porting note: `protected` used to be an attribute below
@[simp]
protected theorem coe_coe {F : Type*} [EquivLike F A₁ A₂] [AlgEquivClass F R A₁ A₂] (f : F) :
    ⇑(f : A₁ ≃ₐ[R] A₂) = f :=
  rfl
#align alg_equiv.coe_coe AlgEquiv.coe_coe

def toAlgHom : A₁ →ₐ[R] A₂ :=
  { e with
    map_one' := e.map_one
    map_zero' := e.map_zero }
#align alg_equiv.to_alg_hom AlgEquiv.toAlgHom

def refl : A₁ ≃ₐ[R] A₁ :=
  { (1 : A₁ ≃+* A₁) with commutes' := fun _ => rfl }
#align alg_equiv.refl AlgEquiv.refl

def symm (e : A₁ ≃ₐ[R] A₂) : A₂ ≃ₐ[R] A₁ :=
  { e.toRingEquiv.symm with
    commutes' := fun r => by
      rw [← e.toRingEquiv.symm_apply_apply (algebraMap R A₁ r)]
      congr
      change _ = e _
      rw [e.commutes] }
#align alg_equiv.symm AlgEquiv.symm

def Simps.symm_apply (e : A₁ ≃ₐ[R] A₂) : A₂ → A₁ :=
  e.symm
#align alg_equiv.simps.symm_apply AlgEquiv.Simps.symm_apply

def trans (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) : A₁ ≃ₐ[R] A₃ :=
  { e₁.toRingEquiv.trans e₂.toRingEquiv with
    commutes' := fun r => show e₂.toFun (e₁.toFun _) = _ by rw [e₁.commutes', e₂.commutes'] }
#align alg_equiv.trans AlgEquiv.trans

def arrowCongr (e₁ : A₁ ≃ₐ[R] A₁') (e₂ : A₂ ≃ₐ[R] A₂') : (A₁ →ₐ[R] A₂) ≃ (A₁' →ₐ[R] A₂') where
  toFun f := (e₂.toAlgHom.comp f).comp e₁.symm.toAlgHom
  invFun f := (e₂.symm.toAlgHom.comp f).comp e₁.toAlgHom
  left_inv f := by
    simp only [AlgHom.comp_assoc, toAlgHom_eq_coe, symm_comp]
    simp only [← AlgHom.comp_assoc, symm_comp, AlgHom.id_comp, AlgHom.comp_id]
  right_inv f := by
    simp only [AlgHom.comp_assoc, toAlgHom_eq_coe, comp_symm]
    simp only [← AlgHom.comp_assoc, comp_symm, AlgHom.id_comp, AlgHom.comp_id]
#align alg_equiv.arrow_congr AlgEquiv.arrowCongr

def equivCongr (e : A₁ ≃ₐ[R] A₂) (e' : A₁' ≃ₐ[R] A₂') : (A₁ ≃ₐ[R] A₁') ≃ A₂ ≃ₐ[R] A₂' where
  toFun ψ := e.symm.trans (ψ.trans e')
  invFun ψ := e.trans (ψ.trans e'.symm)
  left_inv ψ := by
    ext
    simp_rw [trans_apply, symm_apply_apply]
  right_inv ψ := by
    ext
    simp_rw [trans_apply, apply_symm_apply]

@[simp]
theorem equivCongr_refl : equivCongr AlgEquiv.refl AlgEquiv.refl = Equiv.refl (A₁ ≃ₐ[R] A₁') := by
  ext
  rfl

@[simp]
theorem equivCongr_symm (e : A₁ ≃ₐ[R] A₂) (e' : A₁' ≃ₐ[R] A₂') :
    (equivCongr e e').symm = equivCongr e.symm e'.symm :=
  rfl

@[simp]
theorem equivCongr_trans (e₁₂ : A₁ ≃ₐ[R] A₂) (e₁₂' : A₁' ≃ₐ[R] A₂')
    (e₂₃ : A₂ ≃ₐ[R] A₃) (e₂₃' : A₂' ≃ₐ[R] A₃') :
    (equivCongr e₁₂ e₁₂').trans (equivCongr e₂₃ e₂₃') =
      equivCongr (e₁₂.trans e₂₃) (e₁₂'.trans e₂₃') :=
  rfl

/-- If an algebra morphism has an inverse, it is an algebra isomorphism. -/
@[simps]
def ofAlgHom (f : A₁ →ₐ[R] A₂) (g : A₂ →ₐ[R] A₁) (h₁ : f.comp g = AlgHom.id R A₂)
    (h₂ : g.comp f = AlgHom.id R A₁) : A₁ ≃ₐ[R] A₂ :=
  { f with
    toFun := f
    invFun := g
    left_inv := AlgHom.ext_iff.1 h₂
    right_inv := AlgHom.ext_iff.1 h₁ }
#align alg_equiv.of_alg_hom AlgEquiv.ofAlgHom

def ofBijective (f : A₁ →ₐ[R] A₂) (hf : Function.Bijective f) : A₁ ≃ₐ[R] A₂ :=
  { RingEquiv.ofBijective (f : A₁ →+* A₂) hf, f with }
#align alg_equiv.of_bijective AlgEquiv.ofBijective

def toLinearEquiv (e : A₁ ≃ₐ[R] A₂) : A₁ ≃ₗ[R] A₂ :=
  { e with
    toFun := e
    map_smul' := e.map_smul
    invFun := e.symm }
#align alg_equiv.to_linear_equiv AlgEquiv.toLinearEquiv

def toLinearMap : A₁ →ₗ[R] A₂ :=
  e.toAlgHom.toLinearMap
#align alg_equiv.to_linear_map AlgEquiv.toLinearMap

def ofLinearEquiv : A₁ ≃ₐ[R] A₂ :=
  { l with
    toFun := l
    invFun := l.symm
    map_mul' := map_mul
    commutes' := (AlgHom.ofLinearMap l map_one map_mul : A₁ →ₐ[R] A₂).commutes }
#align alg_equiv.of_linear_equiv AlgEquiv.ofLinearEquivₓ

def ofRingEquiv {f : A₁ ≃+* A₂} (hf : ∀ x, f (algebraMap R A₁ x) = algebraMap R A₂ x) :
    A₁ ≃ₐ[R] A₂ :=
  { f with
    toFun := f
    invFun := f.symm
    commutes' := hf }
#align alg_equiv.of_ring_equiv AlgEquiv.ofRingEquiv

def autCongr (ϕ : A₁ ≃ₐ[R] A₂) : (A₁ ≃ₐ[R] A₁) ≃* A₂ ≃ₐ[R] A₂ where
  __ := equivCongr ϕ ϕ
  toFun ψ := ϕ.symm.trans (ψ.trans ϕ)
  invFun ψ := ϕ.trans (ψ.trans ϕ.symm)
  map_mul' ψ χ := by
    ext
    simp only [mul_apply, trans_apply, symm_apply_apply]
#align alg_equiv.aut_congr AlgEquiv.autCongr

def (f : A₁ ≃ₐ[R] A₁) (a : A₁) : f • a = f a :=
  rfl
#align alg_equiv.smul_def AlgEquiv.smul_def

def (f : A₁ ≃ₐ[R] A₁) (x : A₁ˣ) :
    f • x = Units.map f x := rfl

@[simp]
theorem algebraMap_eq_apply (e : A₁ ≃ₐ[R] A₂) {y : R} {x : A₁} :
    algebraMap R A₂ y = e x ↔ algebraMap R A₁ y = x :=
  ⟨fun h => by simpa using e.symm.toAlgHom.algebraMap_eq_apply h, fun h =>
    e.toAlgHom.algebraMap_eq_apply h⟩
#align alg_equiv.algebra_map_eq_apply AlgEquiv.algebraMap_eq_apply

def toLinearMapHom (R A) [CommSemiring R] [Semiring A] [Algebra R A] :
    (A ≃ₐ[R] A) →* A →ₗ[R] A where
  toFun := AlgEquiv.toLinearMap
  map_one' := rfl
  map_mul' := fun _ _ ↦ rfl

lemma pow_toLinearMap (σ : A₁ ≃ₐ[R] A₁) (n : ℕ) :
    (σ ^ n).toLinearMap = σ.toLinearMap ^ n :=
  (AlgEquiv.toLinearMapHom R A₁).map_pow σ n

@[simp]
lemma one_toLinearMap :
    (1 : A₁ ≃ₐ[R] A₁).toLinearMap = 1 := rfl

/-- The units group of `S →ₐ[R] S` is `S ≃ₐ[R] S`.
See `LinearMap.GeneralLinearGroup.generalLinearEquiv` for the linear map version. -/
@[simps]
def algHomUnitsEquiv (R S : Type*) [CommSemiring R] [Semiring S] [Algebra R S] :
    (S →ₐ[R] S)ˣ ≃* (S ≃ₐ[R] S) where
  toFun := fun f ↦
    { (f : S →ₐ[R] S) with
      invFun := ↑(f⁻¹)
      left_inv := (fun x ↦ show (↑(f⁻¹ * f) : S →ₐ[R] S) x = x by rw [inv_mul_self]; rfl)
      right_inv := (fun x ↦ show (↑(f * f⁻¹) : S →ₐ[R] S) x = x by rw [mul_inv_self]; rfl) }
  invFun := fun f ↦ ⟨f, f.symm, f.comp_symm, f.symm_comp⟩
  left_inv := fun _ ↦ rfl
  right_inv := fun _ ↦ rfl
  map_mul' := fun _ _ ↦ rfl

end Semiring

section CommSemiring

variable [CommSemiring R] [CommSemiring A₁] [CommSemiring A₂]
variable [Algebra R A₁] [Algebra R A₂] (e : A₁ ≃ₐ[R] A₂)

-- Porting note: Added nonrec
nonrec theorem map_prod {ι : Type*} (f : ι → A₁) (s : Finset ι) :
    e (∏ x in s, f x) = ∏ x in s, e (f x) :=
  map_prod _ f s
#align alg_equiv.map_prod AlgEquiv.map_prod

def toAlgEquiv (g : G) : A ≃ₐ[R] A :=
  { MulSemiringAction.toRingEquiv _ _ g, MulSemiringAction.toAlgHom R A g with }
#align mul_semiring_action.to_alg_equiv MulSemiringAction.toAlgEquiv

structure AlgEquiv (R : Type u) (A : Type v) (B : Type w) [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B] extends A ≃ B, A ≃* B, A ≃+ B, A ≃+* B where
  /-- An equivalence of algebras commutes with the action of scalars. -/
  protected commutes' : ∀ r : R, toFun (algebraMap R A r) = algebraMap R B r
#align alg_equiv AlgEquiv

structure preserving
  equivalences. You should extend this class when you extend `AlgEquiv`. -/
class AlgEquivClass (F : Type*) (R A B : outParam (Type*)) [CommSemiring R] [Semiring A]
    [Semiring B] [Algebra R A] [Algebra R B] [EquivLike F A B]
    extends RingEquivClass F A B : Prop where
  /-- An equivalence of algebras commutes with the action of scalars. -/
  commutes : ∀ (f : F) (r : R), f (algebraMap R A r) = algebraMap R B r
#align alg_equiv_class AlgEquivClass