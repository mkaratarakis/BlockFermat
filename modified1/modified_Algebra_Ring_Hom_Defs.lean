def NonUnitalRingHomClass.toNonUnitalRingHom (f : F) : α →ₙ+* β :=
  { (f : α →ₙ* β), (f : α →+ β) with }

/-- Any type satisfying `NonUnitalRingHomClass` can be cast into `NonUnitalRingHom` via
`NonUnitalRingHomClass.toNonUnitalRingHom`. -/
instance : CoeTC F (α →ₙ+* β) :=
  ⟨NonUnitalRingHomClass.toNonUnitalRingHom⟩

end NonUnitalRingHomClass

namespace NonUnitalRingHom

section coe

variable [NonUnitalNonAssocSemiring α] [NonUnitalNonAssocSemiring β]

instance : FunLike (α →ₙ+* β) α β where
  coe f := f.toFun
  coe_injective' f g h := by
    cases f
    cases g
    congr
    apply DFunLike.coe_injective'
    exact h

instance : NonUnitalRingHomClass (α →ₙ+* β) α β where
  map_add := NonUnitalRingHom.map_add'
  map_zero := NonUnitalRingHom.map_zero'
  map_mul f := f.map_mul'

-- Porting note: removed due to new `coe` in Lean4
#noalign non_unital_ring_hom.to_fun_eq_coe

def copy (f : α →ₙ+* β) (f' : α → β) (h : f' = f) : α →ₙ+* β :=
  { f.toMulHom.copy f' h, f.toAddMonoidHom.copy f' h with }
#align non_unital_ring_hom.copy NonUnitalRingHom.copy

def id (α : Type*) [NonUnitalNonAssocSemiring α] : α →ₙ+* α := by
  refine' { toFun := id.. } <;> intros <;> rfl
#align non_unital_ring_hom.id NonUnitalRingHom.id

def comp (g : β →ₙ+* γ) (f : α →ₙ+* β) : α →ₙ+* γ :=
  { g.toMulHom.comp f.toMulHom, g.toAddMonoidHom.comp f.toAddMonoidHom with }
#align non_unital_ring_hom.comp NonUnitalRingHom.comp

def : (1 : α →ₙ+* α) = NonUnitalRingHom.id α :=
  rfl
#align non_unital_ring_hom.one_def NonUnitalRingHom.one_def

def (f g : α →ₙ+* α) : f * g = f.comp g :=
  rfl
#align non_unital_ring_hom.mul_def NonUnitalRingHom.mul_def

def RingHomClass.toRingHom (f : F) : α →+* β :=
  { (f : α →* β), (f : α →+ β) with }

/-- Any type satisfying `RingHomClass` can be cast into `RingHom` via `RingHomClass.toRingHom`. -/
instance : CoeTC F (α →+* β) :=
  ⟨RingHomClass.toRingHom⟩

instance (priority := 100) RingHomClass.toNonUnitalRingHomClass : NonUnitalRingHomClass F α β :=
  { ‹RingHomClass F α β› with }
#align ring_hom_class.to_non_unital_ring_hom_class RingHomClass.toNonUnitalRingHomClass

def copy (f : α →+* β) (f' : α → β) (h : f' = f) : α →+* β :=
  { f.toMonoidWithZeroHom.copy f' h, f.toAddMonoidHom.copy f' h with }
#align ring_hom.copy RingHom.copy

def mk' [NonAssocSemiring α] [NonAssocRing β] (f : α →* β)
    (map_add : ∀ a b, f (a + b) = f a + f b) : α →+* β :=
  { AddMonoidHom.mk' f map_add, f with }
#align ring_hom.mk' RingHom.mk'

def id (α : Type*) [NonAssocSemiring α] : α →+* α := by
  refine' { toFun := _root_.id.. } <;> intros <;> rfl
#align ring_hom.id RingHom.id

def comp (g : β →+* γ) (f : α →+* β) : α →+* γ :=
  { g.toNonUnitalRingHom.comp f.toNonUnitalRingHom with toFun := g ∘ f, map_one' := by simp }
#align ring_hom.comp RingHom.comp

def : (1 : α →+* α) = id α :=
  rfl
#align ring_hom.one_def RingHom.one_def

def (f g : α →+* α) : f * g = f.comp g :=
  rfl
#align ring_hom.mul_def RingHom.mul_def

def mkRingHomOfMulSelfOfTwoNeZero (h : ∀ x, f (x * x) = f x * f x) (h_two : (2 : α) ≠ 0)
    (h_one : f 1 = 1) : β →+* α :=
  { f with
    map_one' := h_one,
    map_mul' := fun x y => by
      have hxy := h (x + y)
      rw [mul_add, add_mul, add_mul, f.map_add, f.map_add, f.map_add, f.map_add, h x, h y, add_mul,
        mul_add, mul_add, ← sub_eq_zero, add_comm (f x * f x + f (y * x)), ← sub_sub, ← sub_sub,
        ← sub_sub, mul_comm y x, mul_comm (f y) (f x)] at hxy
      simp only [add_assoc, add_sub_assoc, add_sub_cancel] at hxy
      rw [sub_sub, ← two_mul, ← add_sub_assoc, ← two_mul, ← mul_sub, mul_eq_zero (M₀ := α),
        sub_eq_zero, or_iff_not_imp_left] at hxy
      exact hxy h_two }
#align add_monoid_hom.mk_ring_hom_of_mul_self_of_two_ne_zero AddMonoidHom.mkRingHomOfMulSelfOfTwoNeZero

structure `RingHom a β`, a.k.a. `α →+* β`, for both types of homomorphisms.

## Main definitions

structure NonUnitalRingHom (α β : Type*) [NonUnitalNonAssocSemiring α]
  [NonUnitalNonAssocSemiring β] extends α →ₙ* β, α →+ β
#align non_unital_ring_hom NonUnitalRingHom

structure RingHom (α : Type*) (β : Type*) [NonAssocSemiring α] [NonAssocSemiring β] extends
  α →* β, α →+ β, α →ₙ+* β, α →*₀ β
#align ring_hom RingHom