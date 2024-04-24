def semilinearMap : M →ₛₗ[σ] M₃ where
  toFun := f
  map_add' := map_add f
  map_smul' := map_smulₛₗ f

/-- Reinterpret an element of a type of semilinear maps as a semilinear map. -/
instance instCoeToSemilinearMap : CoeHead F (M →ₛₗ[σ] M₃) where
  coe f := semilinearMap f

end SemilinearMapClass

namespace LinearMapClass
variable {F : Type*} [Semiring R] [AddCommMonoid M₁] [AddCommMonoid M₂] [Module R M₁] [Module R M₂]
  (f : F) [FunLike F M₁ M₂] [LinearMapClass F R M₁ M₂]

/-- Reinterpret an element of a type of linear maps as a linear map. -/
abbrev linearMap : M₁ →ₗ[R] M₂ := SemilinearMapClass.semilinearMap f

/-- Reinterpret an element of a type of linear maps as a linear map. -/
instance instCoeToLinearMap : CoeHead F (M₁ →ₗ[R] M₂) where
  coe f := SemilinearMapClass.semilinearMap f

end LinearMapClass

namespace LinearMap

section AddCommMonoid

variable [Semiring R] [Semiring S]

section

variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [AddCommMonoid N₁] [AddCommMonoid N₂] [AddCommMonoid N₃]
variable [Module R M] [Module R M₂] [Module S M₃]
variable {σ : R →+* S}

instance instFunLike : FunLike (M →ₛₗ[σ] M₃) M M₃ where
  coe f := f.toFun
  coe_injective' f g h := by
    cases f
    cases g
    congr
    apply DFunLike.coe_injective'
    exact h

instance semilinearMapClass : SemilinearMapClass (M →ₛₗ[σ] M₃) σ M M₃ where
  map_add f := f.map_add'
  map_smulₛₗ := LinearMap.map_smul'
#align linear_map.semilinear_map_class LinearMap.semilinearMapClass

def toDistribMulActionHom (f : M →ₛₗ[σ] M₃) : DistribMulActionHom σ.toMonoidHom M M₃ :=
  { f with map_zero' := show f 0 = 0 from map_zero f }
#align linear_map.to_distrib_mul_action_hom LinearMap.toDistribMulActionHom

def copy (f : M →ₛₗ[σ] M₃) (f' : M → M₃) (h : f' = ⇑f) : M →ₛₗ[σ] M₃ where
  toFun := f'
  map_add' := h.symm ▸ f.map_add'
  map_smul' := h.symm ▸ f.map_smul'
#align linear_map.copy LinearMap.copy

def id : M →ₗ[R] M :=
  { DistribMulActionHom.id R with toFun := _root_.id }
#align linear_map.id LinearMap.id

def id' {σ : R →+* R} [RingHomId σ] : M →ₛₗ[σ] M where
  toFun x := x
  map_add' x y := rfl
  map_smul' r x := by
    have := (RingHomId.eq_id : σ = _)
    subst this
    rfl

@[simp, norm_cast]
theorem id'_coe {σ : R →+* R} [RingHomId σ] : ((id' : M →ₛₗ[σ] M) : M → M) = _root_.id :=
  rfl

end

section

variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [AddCommMonoid N₁] [AddCommMonoid N₂] [AddCommMonoid N₃]
variable [Module R M] [Module R M₂] [Module S M₃]
variable (σ : R →+* S)
variable (fₗ gₗ : M →ₗ[R] M₂) (f g : M →ₛₗ[σ] M₃)

theorem isLinear : IsLinearMap R fₗ :=
  ⟨fₗ.map_add', fₗ.map_smul'⟩
#align linear_map.is_linear LinearMap.isLinear

def toAddMonoidHom : M →+ M₃ where
  toFun := f
  map_zero' := f.map_zero
  map_add' := f.map_add
#align linear_map.to_add_monoid_hom LinearMap.toAddMonoidHom

def restrictScalars (fₗ : M →ₗ[S] M₂) : M →ₗ[R] M₂ where
  toFun := fₗ
  map_add' := fₗ.map_add
  map_smul' := fₗ.map_smul_of_tower
#align linear_map.restrict_scalars LinearMap.restrictScalars

def _root_.RingHom.toSemilinearMap (f : R →+* S) : R →ₛₗ[f] S :=
  { f with
    map_smul' := f.map_mul }
#align ring_hom.to_semilinear_map RingHom.toSemilinearMap

def comp : M₁ →ₛₗ[σ₁₃] M₃ where
  toFun := f ∘ g
  map_add' := by simp only [map_add, forall_const, Function.comp_apply]
  -- Note that #8386 changed `map_smulₛₗ` to `map_smulₛₗ _`

def inverse [Module R M] [Module S M₂] {σ : R →+* S} {σ' : S →+* R} [RingHomInvPair σ σ']
    (f : M →ₛₗ[σ] M₂) (g : M₂ → M) (h₁ : LeftInverse g f) (h₂ : RightInverse g f) :
    M₂ →ₛₗ[σ'] M := by
  dsimp [LeftInverse, Function.RightInverse] at h₁ h₂
  exact
    { toFun := g
      map_add' := fun x y ↦ by rw [← h₁ (g (x + y)), ← h₁ (g x + g y)]; simp [h₂]
      map_smul' := fun a b ↦ by
        dsimp only
        rw [← h₁ (g (a • b)), ← h₁ (σ' a • g b)]
        simp [h₂] }
#align linear_map.inverse LinearMap.inverse

def compHom.toLinearMap {R S : Type*} [Semiring R] [Semiring S] (g : R →+* S) :
    letI := compHom S g; R →ₗ[R] S :=
  letI := compHom S g
  { toFun := (g : R → S)
    map_add' := g.map_add
    map_smul' := g.map_mul }
#align module.comp_hom.to_linear_map Module.compHom.toLinearMap

def toSemilinearMap (fₗ : M →ₑ+[σ.toMonoidHom] M₂) : M →ₛₗ[σ] M₂ :=
  { fₗ with }

instance : SemilinearMapClass (M →ₑ+[σ.toMonoidHom] M₂) σ M M₂ where

instance : CoeTC (M →ₑ+[σ.toMonoidHom] M₂) (M →ₛₗ[σ] M₂) :=
  ⟨toSemilinearMap⟩

/-- A `DistribMulActionHom` between two modules is a linear map. -/
def toLinearMap (fₗ : M →+[R] M₃) : M →ₗ[R] M₃ :=
  { fₗ with }
#align distrib_mul_action_hom.to_linear_map DistribMulActionHom.toLinearMap

def mk' (f : M → M₂) (H : IsLinearMap R f) : M →ₗ[R] M₂ where
  toFun := f
  map_add' := H.1
  map_smul' := H.2
#align is_linear_map.mk' IsLinearMap.mk'

def AddMonoidHom.toNatLinearMap [AddCommMonoid M] [AddCommMonoid M₂] (f : M →+ M₂) : M →ₗ[ℕ] M₂
    where
  toFun := f
  map_add' := f.map_add
  map_smul' := map_nsmul f
#align add_monoid_hom.to_nat_linear_map AddMonoidHom.toNatLinearMap

def AddMonoidHom.toIntLinearMap [AddCommGroup M] [AddCommGroup M₂] (f : M →+ M₂) : M →ₗ[ℤ] M₂
    where
  toFun := f
  map_add' := f.map_add
  map_smul' := map_zsmul f
#align add_monoid_hom.to_int_linear_map AddMonoidHom.toIntLinearMap

def AddMonoidHom.toRatLinearMap [AddCommGroup M] [Module ℚ M] [AddCommGroup M₂] [Module ℚ M₂]
    (f : M →+ M₂) : M →ₗ[ℚ] M₂ :=
  { f with map_smul' := map_rat_smul f }
#align add_monoid_hom.to_rat_linear_map AddMonoidHom.toRatLinearMap

def : (default : M →ₛₗ[σ₁₂] M₂) = 0 :=
  rfl
#align linear_map.default_def LinearMap.default_def

structure IsLinearMap (R : Type u) {M : Type v} {M₂ : Type w} [Semiring R] [AddCommMonoid M]
  [AddCommMonoid M₂] [Module R M] [Module R M₂] (f : M → M₂) : Prop where
  /-- A linear map preserves addition. -/
  map_add : ∀ x y, f (x + y) = f x + f y
  /-- A linear map preserves scalar multiplication. -/
  map_smul : ∀ (c : R) (x), f (c • x) = c • f x
#align is_linear_map IsLinearMap

structure LinearMap {R S : Type*} [Semiring R] [Semiring S] (σ : R →+* S) (M : Type*)
    (M₂ : Type*) [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module S M₂] extends
    AddHom M M₂, MulActionHom σ M M₂
#align linear_map LinearMap

structure on `S` is `Module.compHom S g` . -/
@[simps]
def compHom.toLinearMap {R S : Type*} [Semiring R] [Semiring S] (g : R →+* S) :
    letI := compHom S g; R →ₗ[R] S :=
  letI := compHom S g
  { toFun := (g : R → S)
    map_add' := g.map_add
    map_smul' := g.map_mul }
#align module.comp_hom.to_linear_map Module.compHom.toLinearMap