def toNonUnitalStarAlgHom [NonUnitalStarAlgHomClass F R A B] (f : F) : A →⋆ₙₐ[R] B :=
  { (f : A →ₙₐ[R] B) with
    map_star' := map_star f }

instance [NonUnitalStarAlgHomClass F R A B] : CoeTC F (A →⋆ₙₐ[R] B) :=
  ⟨toNonUnitalStarAlgHom⟩

end NonUnitalStarAlgHomClass

namespace NonUnitalStarAlgHom

section Basic

variable {R A B C D : Type*} [Monoid R]
variable [NonUnitalNonAssocSemiring A] [DistribMulAction R A] [Star A]
variable [NonUnitalNonAssocSemiring B] [DistribMulAction R B] [Star B]
variable [NonUnitalNonAssocSemiring C] [DistribMulAction R C] [Star C]
variable [NonUnitalNonAssocSemiring D] [DistribMulAction R D] [Star D]

instance : FunLike (A →⋆ₙₐ[R] B) A B
    where
  coe f := f.toFun
  coe_injective' := by rintro ⟨⟨⟨⟨f, _⟩, _⟩, _⟩, _⟩ ⟨⟨⟨⟨g, _⟩, _⟩, _⟩, _⟩ h; congr

instance : NonUnitalAlgHomClass (A →⋆ₙₐ[R] B) R A B
    where
  map_smulₛₗ f := f.map_smul'
  map_add f := f.map_add'
  map_zero f := f.map_zero'
  map_mul f := f.map_mul'

instance : NonUnitalStarAlgHomClass (A →⋆ₙₐ[R] B) R A B
    where
  map_star f := f.map_star'

-- Porting note: in mathlib3 we didn't need the `Simps.apply` hint.
/-- See Note [custom simps projection] -/
def Simps.apply (f : A →⋆ₙₐ[R] B) : A → B := f

initialize_simps_projections NonUnitalStarAlgHom
  (toFun → apply)

@[simp]
protected theorem coe_coe {F : Type*} [FunLike F A B] [NonUnitalAlgHomClass F R A B]
    [NonUnitalStarAlgHomClass F R A B] (f : F) :
    ⇑(f : A →⋆ₙₐ[R] B) = f := rfl
#align non_unital_star_alg_hom.coe_coe NonUnitalStarAlgHom.coe_coe

def copy (f : A →⋆ₙₐ[R] B) (f' : A → B) (h : f' = f) : A →⋆ₙₐ[R] B
    where
  toFun := f'
  map_smul' := h.symm ▸ map_smul f
  map_zero' := h.symm ▸ map_zero f
  map_add' := h.symm ▸ map_add f
  map_mul' := h.symm ▸ map_mul f
  map_star' := h.symm ▸ map_star f
#align non_unital_star_alg_hom.copy NonUnitalStarAlgHom.copy

def id : A →⋆ₙₐ[R] A :=
  { (1 : A →ₙₐ[R] A) with map_star' := fun _ => rfl }
#align non_unital_star_alg_hom.id NonUnitalStarAlgHom.id

def comp (f : B →⋆ₙₐ[R] C) (g : A →⋆ₙₐ[R] B) : A →⋆ₙₐ[R] C :=
  { f.toNonUnitalAlgHom.comp g.toNonUnitalAlgHom with
    map_star' := by
      simp only [map_star, NonUnitalAlgHom.toFun_eq_coe, eq_self_iff_true, NonUnitalAlgHom.coe_comp,
        coe_toNonUnitalAlgHom, Function.comp_apply, forall_const] }
#align non_unital_star_alg_hom.comp NonUnitalStarAlgHom.comp

def toStarAlgHom (f : F) : A →⋆ₐ[R] B :=
  { (f : A →ₐ[R] B) with
    map_star' := map_star f }

instance : CoeTC F (A →⋆ₐ[R] B) :=
  ⟨toStarAlgHom⟩

end StarAlgHomClass

namespace StarAlgHom

variable {F R A B C D : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Star A] [Semiring B]
  [Algebra R B] [Star B] [Semiring C] [Algebra R C] [Star C] [Semiring D] [Algebra R D] [Star D]

instance : FunLike (A →⋆ₐ[R] B) A B
    where
  coe f := f.toFun
  coe_injective' := by rintro ⟨⟨⟨⟨⟨f, _⟩, _⟩, _⟩, _⟩, _⟩ ⟨⟨⟨⟨⟨g, _⟩, _⟩, _⟩, _⟩, _⟩ h; congr

instance : AlgHomClass (A →⋆ₐ[R] B) R A B
    where
  map_mul f := f.map_mul'
  map_one f := f.map_one'
  map_add f := f.map_add'
  map_zero f := f.map_zero'
  commutes f := f.commutes'

instance : StarAlgHomClass (A →⋆ₐ[R] B) R A B
    where
  map_star f := f.map_star'

@[simp]
protected theorem coe_coe {F : Type*} [FunLike F A B] [AlgHomClass F R A B]
    [StarAlgHomClass F R A B] (f : F) :
    ⇑(f : A →⋆ₐ[R] B) = f :=
  rfl
#align star_alg_hom.coe_coe StarAlgHom.coe_coe

def Simps.apply (f : A →⋆ₐ[R] B) : A → B := f

initialize_simps_projections StarAlgHom (toFun → apply)

@[simp]
theorem coe_toAlgHom {f : A →⋆ₐ[R] B} : (f.toAlgHom : A → B) = f :=
  rfl
#align star_alg_hom.coe_to_alg_hom StarAlgHom.coe_toAlgHom

def copy (f : A →⋆ₐ[R] B) (f' : A → B) (h : f' = f) : A →⋆ₐ[R] B
    where
  toFun := f'
  map_one' := h.symm ▸ map_one f
  map_mul' := h.symm ▸ map_mul f
  map_zero' := h.symm ▸ map_zero f
  map_add' := h.symm ▸ map_add f
  commutes' := h.symm ▸ AlgHomClass.commutes f
  map_star' := h.symm ▸ map_star f
#align star_alg_hom.copy StarAlgHom.copy

def id : A →⋆ₐ[R] A :=
  { AlgHom.id _ _ with map_star' := fun _ => rfl }
#align star_alg_hom.id StarAlgHom.id

def ofId (R A : Type*) [CommSemiring R] [StarRing R] [Semiring A] [StarMul A]
    [Algebra R A] [StarModule R A] : R →⋆ₐ[R] A :=
  { Algebra.ofId R A with
    toFun := algebraMap R A
    map_star' := by simp [Algebra.algebraMap_eq_smul_one] }

end

instance : Inhabited (A →⋆ₐ[R] A) :=
  ⟨StarAlgHom.id R A⟩

/-- The composition of ⋆-algebra homomorphisms, as a ⋆-algebra homomorphism. -/
def comp (f : B →⋆ₐ[R] C) (g : A →⋆ₐ[R] B) : A →⋆ₐ[R] C :=
  { f.toAlgHom.comp g.toAlgHom with
    map_star' := by
      simp only [map_star, AlgHom.toFun_eq_coe, AlgHom.coe_comp, coe_toAlgHom,
        Function.comp_apply, eq_self_iff_true, forall_const] }
#align star_alg_hom.comp StarAlgHom.comp

def toNonUnitalStarAlgHom (f : A →⋆ₐ[R] B) : A →⋆ₙₐ[R] B :=
  { f with map_smul' := map_smul f }
#align star_alg_hom.to_non_unital_star_alg_hom StarAlgHom.toNonUnitalStarAlgHom

def fst : A × B →⋆ₙₐ[R] A :=
  { NonUnitalAlgHom.fst R A B with map_star' := fun _ => rfl }
#align non_unital_star_alg_hom.fst NonUnitalStarAlgHom.fst

def snd : A × B →⋆ₙₐ[R] B :=
  { NonUnitalAlgHom.snd R A B with map_star' := fun _ => rfl }
#align non_unital_star_alg_hom.snd NonUnitalStarAlgHom.snd

def prod (f : A →⋆ₙₐ[R] B) (g : A →⋆ₙₐ[R] C) : A →⋆ₙₐ[R] B × C :=
  { f.toNonUnitalAlgHom.prod g.toNonUnitalAlgHom with
    map_star' := fun x => by simp [map_star, Prod.star_def] }
#align non_unital_star_alg_hom.prod NonUnitalStarAlgHom.prod

def prodEquiv : (A →⋆ₙₐ[R] B) × (A →⋆ₙₐ[R] C) ≃ (A →⋆ₙₐ[R] B × C)
    where
  toFun f := f.1.prod f.2
  invFun f := ((fst _ _ _).comp f, (snd _ _ _).comp f)
  left_inv f := by ext <;> rfl
  right_inv f := by ext <;> rfl
#align non_unital_star_alg_hom.prod_equiv NonUnitalStarAlgHom.prodEquiv

def inl : A →⋆ₙₐ[R] A × B :=
  prod 1 0
#align non_unital_star_alg_hom.inl NonUnitalStarAlgHom.inl

def inr : B →⋆ₙₐ[R] A × B :=
  prod 0 1
#align non_unital_star_alg_hom.inr NonUnitalStarAlgHom.inr

def fst : A × B →⋆ₐ[R] A :=
  { AlgHom.fst R A B with map_star' := fun _ => rfl }
#align star_alg_hom.fst StarAlgHom.fst

def snd : A × B →⋆ₐ[R] B :=
  { AlgHom.snd R A B with map_star' := fun _ => rfl }
#align star_alg_hom.snd StarAlgHom.snd

def prod (f : A →⋆ₐ[R] B) (g : A →⋆ₐ[R] C) : A →⋆ₐ[R] B × C :=
  { f.toAlgHom.prod g.toAlgHom with map_star' := fun x => by simp [Prod.star_def, map_star] }
#align star_alg_hom.prod StarAlgHom.prod

def prodEquiv : (A →⋆ₐ[R] B) × (A →⋆ₐ[R] C) ≃ (A →⋆ₐ[R] B × C)
    where
  toFun f := f.1.prod f.2
  invFun f := ((fst _ _ _).comp f, (snd _ _ _).comp f)
  left_inv f := by ext <;> rfl
  right_inv f := by ext <;> rfl
#align star_alg_hom.prod_equiv StarAlgHom.prodEquiv

def toStarAlgEquiv {F R A B : Type*} [Add A] [Mul A] [SMul R A] [Star A] [Add B] [Mul B] [SMul R B]
    [Star B] [EquivLike F A B] [NonUnitalAlgEquivClass F R A B] [StarAlgEquivClass F R A B]
    (f : F) : A ≃⋆ₐ[R] B :=
  { (f : A ≃+* B) with
    map_star' := map_star f
    map_smul' := map_smul f}

/-- Any type satisfying `StarAlgEquivClass` can be cast into `StarAlgEquiv` via
`StarAlgEquivClass.toStarAlgEquiv`. -/
instance instCoeHead {F R A B : Type*} [Add A] [Mul A] [SMul R A] [Star A] [Add B] [Mul B]
    [SMul R B] [Star B] [EquivLike F A B] [NonUnitalAlgEquivClass F R A B]
    [StarAlgEquivClass F R A B] : CoeHead F (A ≃⋆ₐ[R] B) :=
  ⟨toStarAlgEquiv⟩

end StarAlgEquivClass

namespace StarAlgEquiv

section Basic

variable {F R A B C : Type*} [Add A] [Add B] [Mul A] [Mul B] [SMul R A] [SMul R B] [Star A]
  [Star B] [Add C] [Mul C] [SMul R C] [Star C]

instance : EquivLike (A ≃⋆ₐ[R] B) A B
    where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by
    rcases f with ⟨⟨⟨_, _, _⟩, _⟩, _⟩
    rcases g with ⟨⟨⟨_, _, _⟩, _⟩, _⟩
    congr

instance : NonUnitalAlgEquivClass (A ≃⋆ₐ[R] B) R A B
    where
  map_mul f := f.map_mul'
  map_add f := f.map_add'
  map_smulₛₗ := map_smul'

instance : StarAlgEquivClass (A ≃⋆ₐ[R] B) R A B
    where
  map_star := map_star'

/-- Helper instance for cases where the inference via `EquivLike` is too hard. -/
instance : FunLike (A ≃⋆ₐ[R] B) A B
    where
  coe f := f.toFun
  coe_injective' := DFunLike.coe_injective

@[simp]
theorem toRingEquiv_eq_coe (e : A ≃⋆ₐ[R] B) : e.toRingEquiv = e :=
  rfl

@[ext]
theorem ext {f g : A ≃⋆ₐ[R] B} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h
#align star_alg_equiv.ext StarAlgEquiv.ext

def refl : A ≃⋆ₐ[R] A :=
  { RingEquiv.refl A with
    map_smul' := fun _ _ => rfl
    map_star' := fun _ => rfl }
#align star_alg_equiv.refl StarAlgEquiv.refl

def symm (e : A ≃⋆ₐ[R] B) : B ≃⋆ₐ[R] A :=
  { e.symm with
    map_star' := fun b => by
      simpa only [apply_inv_apply, inv_apply_apply] using
        congr_arg (inv e) (map_star e (inv e b)).symm
    map_smul' := fun r b => by
      simpa only [apply_inv_apply, inv_apply_apply] using
        congr_arg (inv e) (map_smul e r (inv e b)).symm }
#align star_alg_equiv.symm StarAlgEquiv.symm

def Simps.apply (e : A ≃⋆ₐ[R] B) : A → B := e

/-- See Note [custom simps projection] -/
def Simps.symm_apply (e : A ≃⋆ₐ[R] B) : B → A :=
  e.symm
#align star_alg_equiv.simps.symm_apply StarAlgEquiv.Simps.symm_apply

def trans (e₁ : A ≃⋆ₐ[R] B) (e₂ : B ≃⋆ₐ[R] C) : A ≃⋆ₐ[R] C :=
  { e₁.toRingEquiv.trans
      e₂.toRingEquiv with
    map_smul' := fun r a =>
      show e₂.toFun (e₁.toFun (r • a)) = r • e₂.toFun (e₁.toFun a) by
        rw [e₁.map_smul', e₂.map_smul']
    map_star' := fun a =>
      show e₂.toFun (e₁.toFun (star a)) = star (e₂.toFun (e₁.toFun a)) by
        rw [e₁.map_star', e₂.map_star'] }
#align star_alg_equiv.trans StarAlgEquiv.trans

def ofStarAlgHom (f : F) (g : G) (h₁ : ∀ x, g (f x) = x) (h₂ : ∀ x, f (g x) = x) : A ≃⋆ₐ[R] B
    where
  toFun := f
  invFun := g
  left_inv := h₁
  right_inv := h₂
  map_add' := map_add f
  map_mul' := map_mul f
  map_smul' := map_smul f
  map_star' := map_star f
#align star_alg_equiv.of_star_alg_hom StarAlgEquiv.ofStarAlgHom

def ofBijective (f : F) (hf : Function.Bijective f) : A ≃⋆ₐ[R] B :=
  {
    RingEquiv.ofBijective f
      (hf : Function.Bijective (f : A → B)) with
    toFun := f
    map_star' := map_star f
    map_smul' := map_smul f }
#align star_alg_equiv.of_bijective StarAlgEquiv.ofBijective

structure NonUnitalStarAlgHom (R A B : Type*) [Monoid R] [NonUnitalNonAssocSemiring A]
  [DistribMulAction R A] [Star A] [NonUnitalNonAssocSemiring B] [DistribMulAction R B]
  [Star B] extends A →ₙₐ[R] B where
  /-- By definition, a non-unital ⋆-algebra homomorphism preserves the `star` operation. -/
  map_star' : ∀ a : A, toFun (star a) = star (toFun a)
#align non_unital_star_alg_hom NonUnitalStarAlgHom

structure StarAlgHom (R A B : Type*) [CommSemiring R] [Semiring A] [Algebra R A] [Star A]
  [Semiring B] [Algebra R B] [Star B] extends AlgHom R A B where
  /-- By definition, a ⋆-algebra homomorphism preserves the `star` operation. -/
  map_star' : ∀ x : A, toFun (star x) = star (toFun x)
#align star_alg_hom StarAlgHom

structure does not extend it. -/
structure StarAlgEquiv (R A B : Type*) [Add A] [Add B] [Mul A] [Mul B] [SMul R A] [SMul R B]
  [Star A] [Star B] extends A ≃+* B where
  /-- By definition, a ⋆-algebra equivalence preserves the `star` operation. -/
  map_star' : ∀ a : A, toFun (star a) = star (toFun a)
  /-- By definition, a ⋆-algebra equivalence commutes with the action of scalars. -/
  map_smul' : ∀ (r : R) (a : A), toFun (r • a) = r • toFun a
#align star_alg_equiv StarAlgEquiv