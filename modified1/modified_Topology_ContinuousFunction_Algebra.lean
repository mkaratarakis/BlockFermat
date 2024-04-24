def continuousSubmonoid (α : Type*) (β : Type*) [TopologicalSpace α] [TopologicalSpace β]
    [MulOneClass β] [ContinuousMul β] : Submonoid (α → β) where
  carrier := { f : α → β | Continuous f }
  one_mem' := @continuous_const _ _ _ _ 1
  mul_mem' fc gc := fc.mul gc
#align continuous_submonoid continuousSubmonoid

def continuousSubgroup (α : Type*) (β : Type*) [TopologicalSpace α] [TopologicalSpace β] [Group β]
    [TopologicalGroup β] : Subgroup (α → β) :=
  { continuousSubmonoid α β with inv_mem' := fun fc => Continuous.inv fc }
#align continuous_subgroup continuousSubgroup

def coeFnMonoidHom [Monoid β] [ContinuousMul β] : C(α, β) →* α → β where
  toFun f := f
  map_one' := coe_one
  map_mul' := coe_mul
#align continuous_map.coe_fn_monoid_hom ContinuousMap.coeFnMonoidHom

def _root_.MonoidHom.compLeftContinuous {γ : Type*} [Monoid β] [ContinuousMul β]
    [TopologicalSpace γ] [Monoid γ] [ContinuousMul γ] (g : β →* γ) (hg : Continuous g) :
    C(α, β) →* C(α, γ) where
  toFun f := (⟨g, hg⟩ : C(β, γ)).comp f
  map_one' := ext fun _ => g.map_one
  map_mul' _ _ := ext fun _ => g.map_mul _ _
#align monoid_hom.comp_left_continuous MonoidHom.compLeftContinuous

def compMonoidHom' {γ : Type*} [TopologicalSpace γ] [MulOneClass γ] [ContinuousMul γ]
    (g : C(α, β)) : C(β, γ) →* C(α, γ) where
  toFun f := f.comp g
  map_one' := one_comp g
  map_mul' f₁ f₂ := mul_comp f₁ f₂ g
#align continuous_map.comp_monoid_hom' ContinuousMap.compMonoidHom'

def continuousSubsemiring (α : Type*) (R : Type*) [TopologicalSpace α] [TopologicalSpace R]
    [NonAssocSemiring R] [TopologicalSemiring R] : Subsemiring (α → R) :=
  { continuousAddSubmonoid α R, continuousSubmonoid α R with }
#align continuous_subsemiring continuousSubsemiring

def continuousSubring (α : Type*) (R : Type*) [TopologicalSpace α] [TopologicalSpace R] [Ring R]
    [TopologicalRing R] : Subring (α → R) :=
  { continuousAddSubgroup α R, continuousSubsemiring α R with }
#align continuous_subring continuousSubring

def _root_.RingHom.compLeftContinuous (α : Type*) {β : Type*} {γ : Type*}
    [TopologicalSpace α]
    [TopologicalSpace β] [Semiring β] [TopologicalSemiring β] [TopologicalSpace γ] [Semiring γ]
    [TopologicalSemiring γ] (g : β →+* γ) (hg : Continuous g) : C(α, β) →+* C(α, γ) :=
  { g.toMonoidHom.compLeftContinuous α hg, g.toAddMonoidHom.compLeftContinuous α hg with }
#align ring_hom.comp_left_continuous RingHom.compLeftContinuous

def coeFnRingHom {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β] [Semiring β]
    [TopologicalSemiring β] : C(α, β) →+* α → β :=
  { (coeFnMonoidHom : C(α, β) →* _),
    (coeFnAddMonoidHom : C(α, β) →+ _) with }
#align continuous_map.coe_fn_ring_hom ContinuousMap.coeFnRingHom

def continuousSubmodule : Submodule R (α → M) :=
  { continuousAddSubgroup α M with
    carrier := { f : α → M | Continuous f }
    smul_mem' := fun c _ hf => hf.const_smul c }
#align continuous_submodule continuousSubmodule

def _root_.ContinuousLinearMap.compLeftContinuous (α : Type*) [TopologicalSpace α]
    (g : M →L[R] M₂) : C(α, M) →ₗ[R] C(α, M₂) :=
  { g.toLinearMap.toAddMonoidHom.compLeftContinuous α g.continuous with
    map_smul' := fun c _ => ext fun _ => g.map_smul' c _ }
#align continuous_linear_map.comp_left_continuous ContinuousLinearMap.compLeftContinuous

def coeFnLinearMap : C(α, M) →ₗ[R] α → M :=
  { (coeFnAddMonoidHom : C(α, M) →+ _) with
    map_smul' := coe_smul }
#align continuous_map.coe_fn_linear_map ContinuousMap.coeFnLinearMap

def continuousSubalgebra : Subalgebra R (α → A) :=
  { continuousSubsemiring α A with
    carrier := { f : α → A | Continuous f }
    algebraMap_mem' := fun r => (continuous_const : Continuous fun _ : α => algebraMap R A r) }
#align continuous_subalgebra continuousSubalgebra

def ContinuousMap.C : R →+* C(α, A) where
  toFun := fun c : R => ⟨fun _ : α => (algebraMap R A) c, continuous_const⟩
  map_one' := by ext _; exact (algebraMap R A).map_one
  map_mul' c₁ c₂ := by ext _; exact (algebraMap R A).map_mul _ _
  map_zero' := by ext _; exact (algebraMap R A).map_zero
  map_add' c₁ c₂ := by ext _; exact (algebraMap R A).map_add _ _
set_option linter.uppercaseLean3 false in
#align continuous_map.C ContinuousMap.C

def AlgHom.compLeftContinuous {α : Type*} [TopologicalSpace α] (g : A →ₐ[R] A₂)
    (hg : Continuous g) : C(α, A) →ₐ[R] C(α, A₂) :=
  { g.toRingHom.compLeftContinuous α hg with
    commutes' := fun _ => ContinuousMap.ext fun _ => g.commutes' _ }
#align alg_hom.comp_left_continuous AlgHom.compLeftContinuous

def ContinuousMap.compRightAlgHom {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (f : C(α, β)) : C(β, A) →ₐ[R] C(α, A) where
  toFun g := g.comp f
  map_zero' := ext fun _ ↦ rfl
  map_add'  _ _ := ext fun _ ↦ rfl
  map_one' := ext fun _ ↦ rfl
  map_mul' _ _ := ext fun _ ↦ rfl
  commutes' _ := ext fun _ ↦ rfl
#align continuous_map.comp_right_alg_hom ContinuousMap.compRightAlgHom

def ContinuousMap.coeFnAlgHom : C(α, A) →ₐ[R] α → A :=
  { (ContinuousMap.coeFnRingHom : C(α, A) →+* _) with
    commutes' := fun _ => rfl }
#align continuous_map.coe_fn_alg_hom ContinuousMap.coeFnAlgHom

def Set.SeparatesPointsStrongly (s : Set C(α, 𝕜)) : Prop :=
  ∀ (v : α → 𝕜) (x y : α), ∃ f ∈ s, (f x : 𝕜) = v x ∧ f y = v y
#align set.separates_points_strongly Set.SeparatesPointsStrongly

def compStarAlgHom' (f : C(X, Y)) : C(Y, A) →⋆ₐ[𝕜] C(X, A) where
  toFun g := g.comp f
  map_one' := one_comp _
  map_mul' _ _ := rfl
  map_zero' := zero_comp f
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl
#align continuous_map.comp_star_alg_hom' ContinuousMap.compStarAlgHom'

def compStarAlgHom (φ : A →⋆ₐ[𝕜] B) (hφ : Continuous φ) :
    C(X, A) →⋆ₐ[𝕜] C(X, B) where
  toFun f := (⟨φ, hφ⟩ : C(A, B)).comp f
  map_one' := ext fun _ => map_one φ
  map_mul' f g := ext fun x => map_mul φ (f x) (g x)
  map_zero' := ext fun _ => map_zero φ
  map_add' f g := ext fun x => map_add φ (f x) (g x)
  commutes' r := ext fun _x => AlgHomClass.commutes φ r
  map_star' f := ext fun x => map_star φ (f x)

/-- `ContinuousMap.compStarAlgHom` sends the identity `StarAlgHom` on `A` to the identity
`StarAlgHom` on `C(X, A)`. -/
lemma compStarAlgHom_id : compStarAlgHom X (.id 𝕜 A) continuous_id = .id 𝕜 C(X, A) := rfl

/-- `ContinuousMap.compStarAlgHom` is functorial. -/
lemma compStarAlgHom_comp (φ : A →⋆ₐ[𝕜] B) (ψ : B →⋆ₐ[𝕜] C) (hφ : Continuous φ)
    (hψ : Continuous ψ) : compStarAlgHom X (ψ.comp φ) (hψ.comp hφ) =
      (compStarAlgHom X ψ hψ).comp (compStarAlgHom X φ hφ) :=
  rfl

end Postcomposition

section Periodicity

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-! ### Summing translates of a function -/

def compStarAlgEquiv' (f : X ≃ₜ Y) : C(Y, A) ≃⋆ₐ[𝕜] C(X, A) :=
  { f.toContinuousMap.compStarAlgHom' 𝕜 A with
    toFun := (f : C(X, Y)).compStarAlgHom' 𝕜 A
    invFun := (f.symm : C(Y, X)).compStarAlgHom' 𝕜 A
    left_inv := fun g => by
      simp only [ContinuousMap.compStarAlgHom'_apply, ContinuousMap.comp_assoc,
        toContinuousMap_comp_symm, ContinuousMap.comp_id]
    right_inv := fun g => by
      simp only [ContinuousMap.compStarAlgHom'_apply, ContinuousMap.comp_assoc,
        symm_comp_toContinuousMap, ContinuousMap.comp_id]
    map_smul' := fun k a => map_smul (f.toContinuousMap.compStarAlgHom' 𝕜 A) k a }
#align homeomorph.comp_star_alg_equiv' Homeomorph.compStarAlgEquiv'

structure on `continuousSubgroup α β`),
one should use `C(α, β)` with the appropriate instance of the structure.
-/


--attribute [elab_without_expected_type] Continuous.comp

namespace ContinuousFunctions

variable {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β]
variable {f g : { f : α → β | Continuous f }}

instance : CoeFun { f : α → β | Continuous f } fun _ => α → β :=
  ⟨Subtype.val⟩

end ContinuousFunctions

namespace ContinuousMap

variable {α : Type*} {β : Type*} {γ : Type*}
variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

/-! ### `mul` and `add` -/

structure

In this section we show that continuous functions valued in a topological group inherit
the structure of a group.
-/


section Subtype

/-- The `Submonoid` of continuous maps `α → β`. -/
@[to_additive "The `AddSubmonoid` of continuous maps `α → β`. "]
def continuousSubmonoid (α : Type*) (β : Type*) [TopologicalSpace α] [TopologicalSpace β]
    [MulOneClass β] [ContinuousMul β] : Submonoid (α → β) where
  carrier := { f : α → β | Continuous f }
  one_mem' := @continuous_const _ _ _ _ 1
  mul_mem' fc gc := fc.mul gc
#align continuous_submonoid continuousSubmonoid

structure

In this section we show that continuous functions valued in a topological semiring `R` inherit
the structure of a ring.
-/


section Subtype

/-- The subsemiring of continuous maps `α → β`. -/
def continuousSubsemiring (α : Type*) (R : Type*) [TopologicalSpace α] [TopologicalSpace R]
    [NonAssocSemiring R] [TopologicalSemiring R] : Subsemiring (α → R) :=
  { continuousAddSubmonoid α R, continuousSubmonoid α R with }
#align continuous_subsemiring continuousSubsemiring

structure

In this section we show that continuous functions valued in a topological module `M` over a
topological semiring `R` inherit the structure of a module.
-/


section Subtype

variable (α : Type*) [TopologicalSpace α]
variable (R : Type*) [Semiring R]
variable (M : Type*) [TopologicalSpace M] [AddCommGroup M]
variable [Module R M] [ContinuousConstSMul R M] [TopologicalAddGroup M]

/-- The `R`-submodule of continuous maps `α → M`. -/
def continuousSubmodule : Submodule R (α → M) :=
  { continuousAddSubgroup α M with
    carrier := { f : α → M | Continuous f }
    smul_mem' := fun c _ hf => hf.const_smul c }
#align continuous_submodule continuousSubmodule

structure

In this section we show that continuous functions valued in a topological algebra `A` over a ring
`R` inherit the structure of an algebra. Note that the hypothesis that `A` is a topological algebra
is obtained by requiring that `A` be both a `ContinuousSMul` and a `TopologicalSemiring`. -/


section Subtype

variable {α : Type*} [TopologicalSpace α] {R : Type*} [CommSemiring R] {A : Type*}
  [TopologicalSpace A] [Semiring A] [Algebra R A] [TopologicalSemiring A]

/-- The `R`-subalgebra of continuous maps `α → A`. -/
def continuousSubalgebra : Subalgebra R (α → A) :=
  { continuousSubsemiring α A with
    carrier := { f : α → A | Continuous f }
    algebraMap_mem' := fun r => (continuous_const : Continuous fun _ : α => algebraMap R A r) }
#align continuous_subalgebra continuousSubalgebra

structure

If `β` has a continuous star operation, we put a star structure on `C(α, β)` by using the
star operation pointwise.

If `β` is a ⋆-ring, then `C(α, β)` inherits a ⋆-ring structure.

If `β` is a ⋆-ring and a ⋆-module over `R`, then the space of continuous functions from `α` to `β`
is a ⋆-module over `R`.

-/


section StarStructure

variable {R α β : Type*}
variable [TopologicalSpace α] [TopologicalSpace β]

section Star

variable [Star β] [ContinuousStar β]

instance : Star C(α, β) where star f := starContinuousMap.comp f

@[simp]
theorem coe_star (f : C(α, β)) : ⇑(star f) = star (⇑f) :=
  rfl
#align continuous_map.coe_star ContinuousMap.coe_star