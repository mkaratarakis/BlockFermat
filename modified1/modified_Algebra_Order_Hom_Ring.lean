def OrderRingHomClass.toOrderRingHom [NonAssocSemiring α] [Preorder α] [NonAssocSemiring β]
    [Preorder β] [OrderHomClass F α β] [RingHomClass F α β] (f : F) : α →+*o β :=
{ (f : α →+* β) with monotone' := OrderHomClass.monotone f}

/-- Any type satisfying `OrderRingHomClass` can be cast into `OrderRingHom` via
  `OrderRingHomClass.toOrderRingHom`. -/
instance [NonAssocSemiring α] [Preorder α] [NonAssocSemiring β] [Preorder β]
    [OrderHomClass F α β] [RingHomClass F α β] : CoeTC F (α →+*o β) :=
  ⟨OrderRingHomClass.toOrderRingHom⟩

end Hom

section Equiv

variable [EquivLike F α β]

/-- Turn an element of a type `F` satisfying `OrderIsoClass F α β` and `RingEquivClass F α β`
into an actual `OrderRingIso`.
This is declared as the default coercion from `F` to `α ≃+*o β`. -/
@[coe]
def OrderRingIsoClass.toOrderRingIso [Mul α] [Add α] [LE α] [Mul β] [Add β] [LE β]
    [OrderIsoClass F α β] [RingEquivClass F α β] (f : F) : α ≃+*o β :=
{ (f : α ≃+* β) with map_le_map_iff' := map_le_map_iff f}

/-- Any type satisfying `OrderRingIsoClass` can be cast into `OrderRingIso` via
  `OrderRingIsoClass.toOrderRingIso`. -/
instance [Mul α] [Add α] [LE α] [Mul β] [Add β] [LE β] [OrderIsoClass F α β]
    [RingEquivClass F α β] : CoeTC F (α ≃+*o β) :=
  ⟨OrderRingIsoClass.toOrderRingIso⟩

end Equiv

/-! ### Ordered ring homomorphisms -/

def toOrderAddMonoidHom (f : α →+*o β) : α →+o β :=
  { f with }
#align order_ring_hom.to_order_add_monoid_hom OrderRingHom.toOrderAddMonoidHom

def toOrderMonoidWithZeroHom (f : α →+*o β) : α →*₀o β :=
  { f with }
#align order_ring_hom.to_order_monoid_with_zero_hom OrderRingHom.toOrderMonoidWithZeroHom

def copy (f : α →+*o β) (f' : α → β) (h : f' = f) : α →+*o β :=
  { f.toRingHom.copy f' h, f.toOrderAddMonoidHom.copy f' h with }
#align order_ring_hom.copy OrderRingHom.copy

def id : α →+*o α :=
  { RingHom.id _, OrderHom.id with }
#align order_ring_hom.id OrderRingHom.id

def comp (f : β →+*o γ) (g : α →+*o β) : α →+*o γ :=
  { f.toRingHom.comp g.toRingHom, f.toOrderAddMonoidHom.comp g.toOrderAddMonoidHom with }
#align order_ring_hom.comp OrderRingHom.comp

def toOrderIso (f : α ≃+*o β) : α ≃o β :=
  ⟨f.toRingEquiv.toEquiv, f.map_le_map_iff'⟩
#align order_ring_iso.to_order_iso OrderRingIso.toOrderIso

def refl : α ≃+*o α :=
  ⟨RingEquiv.refl α, Iff.rfl⟩
#align order_ring_iso.refl OrderRingIso.refl

def symm (e : α ≃+*o β) : β ≃+*o α :=
  ⟨e.toRingEquiv.symm, by
    intro a b
    erw [← map_le_map_iff e, e.1.apply_symm_apply, e.1.apply_symm_apply]⟩
#align order_ring_iso.symm OrderRingIso.symm

def Simps.symm_apply (e : α ≃+*o β) : β → α :=
  e.symm
#align order_ring_iso.simps.symm_apply OrderRingIso.Simps.symm_apply

def trans (f : α ≃+*o β) (g : β ≃+*o γ) : α ≃+*o γ :=
  ⟨f.toRingEquiv.trans g.toRingEquiv, (map_le_map_iff g).trans (map_le_map_iff f)⟩
#align order_ring_iso.trans OrderRingIso.trans

def toOrderRingHom (f : α ≃+*o β) : α →+*o β :=
  ⟨f.toRingEquiv.toRingHom, fun _ _ => (map_le_map_iff f).2⟩
#align order_ring_iso.to_order_ring_hom OrderRingIso.toOrderRingHom

structure OrderRingHom (α β : Type*) [NonAssocSemiring α] [Preorder α] [NonAssocSemiring β]
  [Preorder β] extends α →+* β where
  /-- The proposition that the function preserves the order. -/
  monotone' : Monotone toFun
#align order_ring_hom OrderRingHom

structure OrderRingIso (α β : Type*) [Mul α] [Mul β] [Add α] [Add β] [LE α] [LE β] extends
  α ≃+* β where
  /-- The proposition that the function preserves the order bijectively. -/
  map_le_map_iff' {a b : α} : toFun a ≤ toFun b ↔ a ≤ b
#align order_ring_iso OrderRingIso