def OrderMonoidHomClass.toOrderMonoidHom [OrderHomClass F α β] [MonoidHomClass F α β] (f : F) :
    α →*o β :=
  { (f : α →* β) with monotone' := OrderHomClass.monotone f }

/-- Any type satisfying `OrderMonoidHomClass` can be cast into `OrderMonoidHom` via
  `OrderMonoidHomClass.toOrderMonoidHom`. -/
@[to_additive "Any type satisfying `OrderAddMonoidHomClass` can be cast into `OrderAddMonoidHom` via
  `OrderAddMonoidHomClass.toOrderAddMonoidHom`"]
instance [OrderHomClass F α β] [MonoidHomClass F α β] : CoeTC F (α →*o β) :=
  ⟨OrderMonoidHomClass.toOrderMonoidHom⟩

end Monoid

section MonoidWithZero

variable [Preorder α] [Preorder β] [MulZeroOneClass α] [MulZeroOneClass β]

/-- `OrderMonoidWithZeroHom α β` is the type of functions `α → β` that preserve
the `MonoidWithZero` structure.

`OrderMonoidWithZeroHom` is also used for group homomorphisms.

When possible, instead of parametrizing results over `(f : α →+ β)`,
you should parametrize over `(F : Type*) [OrderMonoidWithZeroHomClass F α β] (f : F)`.

When you extend this structure, make sure to extend `OrderMonoidWithZeroHomClass`. -/
structure OrderMonoidWithZeroHom (α β : Type*) [Preorder α] [Preorder β] [MulZeroOneClass α]
  [MulZeroOneClass β] extends α →*₀ β where
  /-- An `OrderMonoidWithZeroHom` is a monotone function. -/
  monotone' : Monotone toFun
#align order_monoid_with_zero_hom OrderMonoidWithZeroHom

def OrderMonoidWithZeroHomClass.toOrderMonoidWithZeroHom [OrderHomClass F α β]
    [MonoidWithZeroHomClass F α β] (f : F) : α →*₀o β :=
{ (f : α →*₀ β) with monotone' := OrderHomClass.monotone f }

end

variable [FunLike F α β]

instance [OrderHomClass F α β] [MonoidWithZeroHomClass F α β] : CoeTC F (α →*₀o β) :=
  ⟨OrderMonoidWithZeroHomClass.toOrderMonoidWithZeroHom⟩

end MonoidWithZero

section OrderedZero

variable [FunLike F α β]
variable [Preorder α] [Zero α] [Preorder β] [Zero β] [OrderHomClass F α β]
  [ZeroHomClass F α β] (f : F) {a : α}

/-- See also `NonnegHomClass.apply_nonneg`. -/
theorem map_nonneg (ha : 0 ≤ a) : 0 ≤ f a := by
  rw [← map_zero f]
  exact OrderHomClass.mono _ ha
#align map_nonneg map_nonneg

def toOrderHom (f : α →*o β) : α →o β :=
  { f with }
#align order_monoid_hom.to_order_hom OrderMonoidHom.toOrderHom

def copy (f : α →*o β) (f' : α → β) (h : f' = f) : α →*o β :=
  { f.toMonoidHom.copy f' h with toFun := f', monotone' := h.symm.subst f.monotone' }
#align order_monoid_hom.copy OrderMonoidHom.copy

def id : α →*o α :=
  { MonoidHom.id α, OrderHom.id with }
#align order_monoid_hom.id OrderMonoidHom.id

def comp (f : β →*o γ) (g : α →*o β) : α →*o γ :=
  { f.toMonoidHom.comp (g : α →* β), f.toOrderHom.comp (g : α →o β) with }
#align order_monoid_hom.comp OrderMonoidHom.comp

def mk' (f : α → β) (hf : Monotone f) (map_mul : ∀ a b : α, f (a * b) = f a * f b) : α →*o β :=
  { MonoidHom.mk' f map_mul with monotone' := hf }
#align order_monoid_hom.mk' OrderMonoidHom.mk'

def toOrderMonoidHom (f : α →*₀o β) : α →*o β :=
  { f with }
#align order_monoid_with_zero_hom.to_order_monoid_hom OrderMonoidWithZeroHom.toOrderMonoidHom

def copy (f : α →*₀o β) (f' : α → β) (h : f' = f) : α →*o β :=
  { f.toOrderMonoidHom.copy f' h, f.toMonoidWithZeroHom.copy f' h with toFun := f' }
#align order_monoid_with_zero_hom.copy OrderMonoidWithZeroHom.copy

def id : α →*₀o α :=
  { MonoidWithZeroHom.id α, OrderHom.id with }
#align order_monoid_with_zero_hom.id OrderMonoidWithZeroHom.id

def comp (f : β →*₀o γ) (g : α →*₀o β) : α →*₀o γ :=
  { f.toMonoidWithZeroHom.comp (g : α →*₀ β), f.toOrderMonoidHom.comp (g : α →*o β) with }
#align order_monoid_with_zero_hom.comp OrderMonoidWithZeroHom.comp

structure OrderAddMonoidHom (α β : Type*) [Preorder α] [Preorder β] [AddZeroClass α]
  [AddZeroClass β] extends α →+ β where
  /-- An `OrderAddMonoidHom` is a monotone function. -/
  monotone' : Monotone toFun
#align order_add_monoid_hom OrderAddMonoidHom

structure OrderMonoidHom (α β : Type*) [Preorder α] [Preorder β] [MulOneClass α]
  [MulOneClass β] extends α →* β where
  /-- An `OrderMonoidHom` is a monotone function. -/
  monotone' : Monotone toFun
#align order_monoid_hom OrderMonoidHom

structure OrderMonoidWithZeroHom (α β : Type*) [Preorder α] [Preorder β] [MulZeroOneClass α]
  [MulZeroOneClass β] extends α →*₀ β where
  /-- An `OrderMonoidWithZeroHom` is a monotone function. -/
  monotone' : Monotone toFun
#align order_monoid_with_zero_hom OrderMonoidWithZeroHom