def toNonUnitalAlgSemiHom {F R S : Type*} [Monoid R] [Monoid S] {φ : R →* S} {A B : Type*}
    [NonUnitalNonAssocSemiring A] [DistribMulAction R A]
    [NonUnitalNonAssocSemiring B] [DistribMulAction S B] [FunLike F A B]
    [NonUnitalAlgSemiHomClass F φ A B] (f : F) : A →ₛₙₐ[φ] B :=
  { (f : A →ₙ+* B) with
    toFun := f
    map_smul' := map_smulₛₗ f }

instance {F R S A B : Type*} [Monoid R] [Monoid S] {φ : R →* S}
    [NonUnitalNonAssocSemiring A] [DistribMulAction R A]
    [NonUnitalNonAssocSemiring B] [DistribMulAction S B] [FunLike F A B]
    [NonUnitalAlgSemiHomClass F φ A B] :
      CoeTC F (A →ₛₙₐ[φ] B) :=
  ⟨toNonUnitalAlgSemiHom⟩

/-- Turn an element of a type `F` satisfying `NonUnitalAlgHomClass F R A B` into an actual
@[coe]
`NonUnitalAlgHom`. This is declared as the default coercion from `F` to `A →ₛₙₐ[R] B`. -/
def toNonUnitalAlgHom {F R : Type*} [Monoid R] {A B : Type*}
    [NonUnitalNonAssocSemiring A] [DistribMulAction R A]
    [NonUnitalNonAssocSemiring B] [DistribMulAction R B]
    [FunLike F A B] [NonUnitalAlgHomClass F R A B] (f : F) : A →ₙₐ[R] B :=
  { (f : A →ₙ+* B) with
    toFun := f
    map_smul' := map_smulₛₗ f }

instance {F R : Type*} [Monoid R] {A B : Type*}
    [NonUnitalNonAssocSemiring A] [DistribMulAction R A]
    [NonUnitalNonAssocSemiring B] [DistribMulAction R B]
    [FunLike F A B] [NonUnitalAlgHomClass F R A B] :
    CoeTC F (A →ₙₐ[R] B) :=
  ⟨toNonUnitalAlgHom⟩

end NonUnitalAlgHomClass

namespace NonUnitalAlgHom

variable {T : Type*} [Monoid R] [Monoid S] [Monoid T] (φ : R →* S)
variable (A : Type v) (B : Type w) (C : Type w₁)
variable [NonUnitalNonAssocSemiring A] [DistribMulAction R A]
variable [NonUnitalNonAssocSemiring B] [DistribMulAction S B]
variable [NonUnitalNonAssocSemiring C] [DistribMulAction T C]

-- Porting note: Replaced with DFunLike instance
-- /-- see Note [function coercion] -/
-- instance : CoeFun (A →ₙₐ[R] B) fun _ => A → B :=
--   ⟨toFun⟩

instance  : DFunLike (A →ₛₙₐ[φ] B) A fun _ => B where
  coe f := f.toFun
  coe_injective' := by rintro ⟨⟨⟨f, _⟩, _⟩, _⟩ ⟨⟨⟨g, _⟩, _⟩, _⟩ h; congr

@[simp]
theorem toFun_eq_coe (f : A →ₛₙₐ[φ] B) : f.toFun = ⇑f :=
  rfl
#align non_unital_alg_hom.to_fun_eq_coe NonUnitalAlgHom.toFun_eq_coe

def Simps.apply (f : A →ₛₙₐ[φ] B) : A → B := f

initialize_simps_projections NonUnitalAlgHom
  (toDistribMulActionHom_toMulActionHom_toFun → apply, -toDistribMulActionHom)

variable {φ A B C}
@[simp]
protected theorem coe_coe {F : Type*} [FunLike F A B]
    [NonUnitalAlgSemiHomClass F φ A B] (f : F) :
    ⇑(f : A →ₛₙₐ[φ] B) = f :=
  rfl
#align non_unital_alg_hom.coe_coe NonUnitalAlgHom.coe_coe

def id (R A : Type*) [Monoid R] [NonUnitalNonAssocSemiring A]
    [DistribMulAction R A] : A →ₙₐ[R] A :=
  { NonUnitalRingHom.id A with
    toFun := id
    map_smul' := fun _ _ => rfl }

@[simp]
theorem coe_id : ⇑(NonUnitalAlgHom.id R A) = id :=
  rfl

instance : Zero (A →ₛₙₐ[φ] B) :=
  ⟨{ (0 : A →ₑ+[φ] B) with map_mul' := by simp }⟩

instance : One (A →ₙₐ[R] A) :=
  ⟨NonUnitalAlgHom.id R A⟩

@[simp]
theorem coe_zero : ⇑(0 : A →ₛₙₐ[φ] B) = 0 :=
  rfl
#align non_unital_alg_hom.coe_zero NonUnitalAlgHom.coe_zero

def comp (f : B →ₛₙₐ[ψ] C) (g : A →ₛₙₐ[φ] B) [κ : MonoidHom.CompTriple φ ψ χ]:
    A →ₛₙₐ[χ] C :=
  { (f : B →ₙ* C).comp (g : A →ₙ* B), (f : B →ₑ+[ψ] C).comp (g : A →ₑ+[φ] B) with }
#align non_unital_alg_hom.comp NonUnitalAlgHom.comp

def inverse (f : A →ₙₐ[R] B₁) (g : B₁ → A)
    (h₁ : Function.LeftInverse g f)
    (h₂ : Function.RightInverse g f) : B₁ →ₙₐ[R] A :=
  { (f : A →ₙ* B₁).inverse g h₁ h₂, (f : A →+[R] B₁).inverse g h₁ h₂ with }
#align non_unital_alg_hom.inverse NonUnitalAlgHom.inverse

def inverse' (f : A →ₛₙₐ[φ] B) (g : B → A)
    (k : Function.RightInverse φ' φ)
    (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) :
    B →ₛₙₐ[φ'] A :=
  { (f : A →ₙ* B).inverse g h₁ h₂, (f : A →ₑ+[φ] B).inverse' g k h₁ h₂ with
    map_zero' := by
      simp only [MulHom.toFun_eq_coe, MulHom.inverse_apply]
      rw [← f.map_zero, h₁]
    map_add' := fun x y ↦ by
      simp only [MulHom.toFun_eq_coe, MulHom.inverse_apply]
      rw [← h₂ x, ← h₂ y, ← map_add, h₁, h₂, h₂] }

@[simp]
theorem coe_inverse' (f : A →ₛₙₐ[φ] B) (g : B → A)
    (k : Function.RightInverse φ' φ)
    (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) :
    (inverse' f g k h₁ h₂ : B → A) = g :=
  rfl

/-! ### Operations on the product type

def fst : A × B →ₙₐ[R] A where
  toFun := Prod.fst
  map_zero' := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_mul' _ _ := rfl
#align non_unital_alg_hom.fst NonUnitalAlgHom.fst

def snd : A × B →ₙₐ[R] B where
  toFun := Prod.snd
  map_zero' := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_mul' _ _ := rfl
#align non_unital_alg_hom.snd NonUnitalAlgHom.snd

def prod (f : A →ₙₐ[R] B) (g : A →ₙₐ[R] C) : A →ₙₐ[R] B × C
    where
  toFun := Pi.prod f g
  map_zero' := by simp only [Pi.prod, Prod.zero_eq_mk, map_zero]
  map_add' x y := by simp only [Pi.prod, Prod.mk_add_mk, map_add]
  map_mul' x y := by simp only [Pi.prod, Prod.mk_mul_mk, map_mul]
  map_smul' c x := by simp only [Pi.prod, map_smul, MonoidHom.id_apply, id_eq, Prod.smul_mk]
#align non_unital_alg_hom.prod NonUnitalAlgHom.prod

def prodEquiv : (A →ₙₐ[R] B) × (A →ₙₐ[R] C) ≃ (A →ₙₐ[R] B × C)
    where
  toFun f := f.1.prod f.2
  invFun f := ((fst _ _ _).comp f, (snd _ _ _).comp f)
  left_inv _ := rfl
  right_inv _ := rfl
#align non_unital_alg_hom.prod_equiv NonUnitalAlgHom.prodEquiv

def inl : A →ₙₐ[R] A × B :=
  prod 1 0
#align non_unital_alg_hom.inl NonUnitalAlgHom.inl

def inr : B →ₙₐ[R] A × B :=
  prod 0 1
#align non_unital_alg_hom.inr NonUnitalAlgHom.inr

def toNonUnitalAlgHom (f : A →ₐ[R] B) : A →ₙₐ[R] B :=
  { f with map_smul' := map_smul f }
#align alg_hom.to_non_unital_alg_hom AlgHom.toNonUnitalAlgHom

structure NonUnitalAlgHom [Monoid R] [Monoid S] (φ : R →* S) (A : Type v) (B : Type w)
    [NonUnitalNonAssocSemiring A] [DistribMulAction R A]
    [NonUnitalNonAssocSemiring B] [DistribMulAction S B] extends A →ₑ+[φ] B, A →ₙ* B

#align non_unital_alg_hom NonUnitalAlgHom