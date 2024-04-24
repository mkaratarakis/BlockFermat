def toAlgHom {F : Type*} [FunLike F A B] [AlgHomClass F R A B] (f : F) : A →ₐ[R] B where
  __ := (f : A →+* B)
  toFun := f
  commutes' := AlgHomClass.commutes f

instance coeTC {F : Type*} [FunLike F A B] [AlgHomClass F R A B] : CoeTC F (A →ₐ[R] B) :=
  ⟨AlgHomClass.toAlgHom⟩
#align alg_hom_class.alg_hom.has_coe_t AlgHomClass.coeTC

def Simps.apply {R : Type u} {α : Type v} {β : Type w} [CommSemiring R]
    [Semiring α] [Semiring β] [Algebra R α] [Algebra R β] (f : α →ₐ[R] β) : α → β := f

initialize_simps_projections AlgHom (toFun → apply)

@[simp]
protected theorem coe_coe {F : Type*} [FunLike F A B] [AlgHomClass F R A B] (f : F) :
    ⇑(f : A →ₐ[R] B) = f :=
  rfl
#align alg_hom.coe_coe AlgHom.coe_coe

def toMonoidHom' (f : A →ₐ[R] B) : A →* B := (f : A →+* B)

instance coeOutMonoidHom : CoeOut (A →ₐ[R] B) (A →* B) :=
  ⟨AlgHom.toMonoidHom'⟩
#align alg_hom.coe_monoid_hom AlgHom.coeOutMonoidHom

def toAddMonoidHom' (f : A →ₐ[R] B) : A →+ B := (f : A →+* B)

instance coeOutAddMonoidHom : CoeOut (A →ₐ[R] B) (A →+ B) :=
  ⟨AlgHom.toAddMonoidHom'⟩
#align alg_hom.coe_add_monoid_hom AlgHom.coeOutAddMonoidHom

def mk' (f : A →+* B) (h : ∀ (c : R) (x), f (c • x) = c • f x) : A →ₐ[R] B :=
  { f with
    toFun := f
    commutes' := fun c => by simp only [Algebra.algebraMap_eq_smul_one, h, f.map_one] }
#align alg_hom.mk' AlgHom.mk'

def id : A →ₐ[R] A :=
  { RingHom.id A with commutes' := fun _ => rfl }
#align alg_hom.id AlgHom.id

def comp (φ₁ : B →ₐ[R] C) (φ₂ : A →ₐ[R] B) : A →ₐ[R] C :=
  { φ₁.toRingHom.comp ↑φ₂ with
    commutes' := fun r : R => by rw [← φ₁.commutes, ← φ₂.commutes]; rfl }
#align alg_hom.comp AlgHom.comp

def toLinearMap : A →ₗ[R] B where
  toFun := φ
  map_add' := map_add _
  map_smul' := map_smul _
#align alg_hom.to_linear_map AlgHom.toLinearMap

def ofLinearMap (f : A →ₗ[R] B) (map_one : f 1 = 1) (map_mul : ∀ x y, f (x * y) = f x * f y) :
    A →ₐ[R] B :=
  { f.toAddMonoidHom with
    toFun := f
    map_one' := map_one
    map_mul' := map_mul
    commutes' := fun c => by simp only [Algebra.algebraMap_eq_smul_one, f.map_smul, map_one] }
#align alg_hom.of_linear_map AlgHom.ofLinearMap

def toNatAlgHom [Semiring R] [Semiring S] (f : R →+* S) : R →ₐ[ℕ] S :=
  { f with
    toFun := f
    commutes' := fun n => by simp }
#align ring_hom.to_nat_alg_hom RingHom.toNatAlgHom

def toIntAlgHom [Ring R] [Ring S] [Algebra ℤ R] [Algebra ℤ S] (f : R →+* S) : R →ₐ[ℤ] S :=
  { f with commutes' := fun n => by simp }
#align ring_hom.to_int_alg_hom RingHom.toIntAlgHom

def toRatAlgHom [Ring R] [Ring S] [Algebra ℚ R] [Algebra ℚ S] (f : R →+* S) : R →ₐ[ℚ] S :=
  { f with commutes' := f.map_rat_algebraMap }
#align ring_hom.to_rat_alg_hom RingHom.toRatAlgHom

def RingHom.equivRatAlgHom [Ring R] [Ring S] [Algebra ℚ R] [Algebra ℚ S] : (R →+* S) ≃ (R →ₐ[ℚ] S)
    where
  toFun := RingHom.toRatAlgHom
  invFun := AlgHom.toRingHom
  left_inv f := RingHom.toRatAlgHom_toRingHom f
  right_inv f := AlgHom.toRingHom_toRatAlgHom f
#align ring_hom.equiv_rat_alg_hom RingHom.equivRatAlgHom

def ofId : R →ₐ[R] A :=
  { algebraMap R A with commutes' := fun _ => rfl }
#align algebra.of_id Algebra.ofId

def (f : A →ₐ[R] A) (x : Aˣ) :
    f • x = Units.map (f : A →* A) x := rfl

end MulDistribMulAction
end Algebra

namespace MulSemiringAction

variable {M G : Type*} (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]
variable [Monoid M] [MulSemiringAction M A] [SMulCommClass M R A]

/-- Each element of the monoid defines an algebra homomorphism.

This is a stronger version of `MulSemiringAction.toRingHom` and
`DistribMulAction.toLinearMap`. -/
@[simps]
def toAlgHom (m : M) : A →ₐ[R] A :=
  { MulSemiringAction.toRingHom _ _ m with
    toFun := fun a => m • a
    commutes' := smul_algebraMap _ }
#align mul_semiring_action.to_alg_hom MulSemiringAction.toAlgHom

structure AlgHom (R : Type u) (A : Type v) (B : Type w) [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B] extends RingHom A B where
  commutes' : ∀ r : R, toFun (algebraMap R A r) = algebraMap R B r
#align alg_hom AlgHom