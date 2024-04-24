def nonUnitalRingHom {γ : Type w} [∀ i, NonUnitalNonAssocSemiring (f i)]
    [NonUnitalNonAssocSemiring γ] (g : ∀ i, γ →ₙ+* f i) : γ →ₙ+* ∀ i, f i :=
  { Pi.mulHom fun i => (g i).toMulHom, Pi.addMonoidHom fun i => (g i).toAddMonoidHom with
    toFun := fun x b => g b x }
#align pi.non_unital_ring_hom Pi.nonUnitalRingHom

def ringHom {γ : Type w} [∀ i, NonAssocSemiring (f i)] [NonAssocSemiring γ]
    (g : ∀ i, γ →+* f i) : γ →+* ∀ i, f i :=
  { Pi.monoidHom fun i => (g i).toMonoidHom, Pi.addMonoidHom fun i => (g i).toAddMonoidHom with
    toFun := fun x b => g b x }
#align pi.ring_hom Pi.ringHom

def Pi.evalNonUnitalRingHom (f : I → Type v) [∀ i, NonUnitalNonAssocSemiring (f i)] (i : I) :
    (∀ i, f i) →ₙ+* f i :=
  { Pi.evalMulHom f i, Pi.evalAddMonoidHom f i with }
#align pi.eval_non_unital_ring_hom Pi.evalNonUnitalRingHom

def Pi.constNonUnitalRingHom (α β : Type*) [NonUnitalNonAssocSemiring β] : β →ₙ+* α → β :=
  { Pi.nonUnitalRingHom fun _ => NonUnitalRingHom.id β with toFun := Function.const _ }
#align pi.const_non_unital_ring_hom Pi.constNonUnitalRingHom

def NonUnitalRingHom.compLeft {α β : Type*} [NonUnitalNonAssocSemiring α]
    [NonUnitalNonAssocSemiring β] (f : α →ₙ+* β) (I : Type*) : (I → α) →ₙ+* I → β :=
  { f.toMulHom.compLeft I, f.toAddMonoidHom.compLeft I with toFun := fun h => f ∘ h }
#align non_unital_ring_hom.comp_left NonUnitalRingHom.compLeft

def Pi.evalRingHom (f : I → Type v) [∀ i, NonAssocSemiring (f i)] (i : I) : (∀ i, f i) →+* f i :=
  { Pi.evalMonoidHom f i, Pi.evalAddMonoidHom f i with }
#align pi.eval_ring_hom Pi.evalRingHom

def Pi.constRingHom (α β : Type*) [NonAssocSemiring β] : β →+* α → β :=
  { Pi.ringHom fun _ => RingHom.id β with toFun := Function.const _ }
#align pi.const_ring_hom Pi.constRingHom

def RingHom.compLeft {α β : Type*} [NonAssocSemiring α] [NonAssocSemiring β]
    (f : α →+* β) (I : Type*) : (I → α) →+* I → β :=
  { f.toMonoidHom.compLeft I, f.toAddMonoidHom.compLeft I with toFun := fun h => f ∘ h }
#align ring_hom.comp_left RingHom.compLeft