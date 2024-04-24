def MonoidWithZeroHomClass.toMonoidWithZeroHom [FunLike F α β] [MonoidWithZeroHomClass F α β]
    (f : F) : α →*₀ β := { (f : α →* β), (f : ZeroHom α β) with }

/-- Any type satisfying `MonoidWithZeroHomClass` can be cast into `MonoidWithZeroHom` via
`MonoidWithZeroHomClass.toMonoidWithZeroHom`. -/
instance [FunLike F α β] [MonoidWithZeroHomClass F α β] : CoeTC F (α →*₀ β) :=
  ⟨MonoidWithZeroHomClass.toMonoidWithZeroHom⟩

namespace MonoidWithZeroHom

attribute [nolint docBlame] toMonoidHom
attribute [nolint docBlame] toZeroHom

instance funLike : FunLike (α →*₀ β) α β where
  coe f := f.toFun
  coe_injective' f g h := by obtain ⟨⟨_, _⟩, _⟩ := f; obtain ⟨⟨_, _⟩, _⟩ := g; congr

instance monoidWithZeroHomClass : MonoidWithZeroHomClass (α →*₀ β) α β where
  map_mul := MonoidWithZeroHom.map_mul'
  map_one := MonoidWithZeroHom.map_one'
  map_zero f := f.map_zero'
#align monoid_with_zero_hom.monoid_with_zero_hom_class MonoidWithZeroHom.monoidWithZeroHomClass

def copy (f : α →*₀ β) (f' : α → β) (h : f' = f) : α →* β :=
  { f.toZeroHom.copy f' h, f.toMonoidHom.copy f' h with }
#align monoid_with_zero_hom.copy MonoidWithZeroHom.copy

def id (α : Type*) [MulZeroOneClass α] : α →*₀ α where
  toFun x := x
  map_zero' := rfl
  map_one' := rfl
  map_mul' _ _ := rfl
#align monoid_with_zero_hom.id MonoidWithZeroHom.id

def comp (hnp : β →*₀ γ) (hmn : α →*₀ β) : α →*₀ γ where
  toFun := hnp ∘ hmn
  map_zero' := by rw [comp_apply, map_zero, map_zero]
  map_one' := by simp
  map_mul' := by simp
#align monoid_with_zero_hom.comp MonoidWithZeroHom.comp

structure MonoidWithZeroHom (α β : Type*) [MulZeroOneClass α] [MulZeroOneClass β]
  extends ZeroHom α β, MonoidHom α β
#align monoid_with_zero_hom MonoidWithZeroHom