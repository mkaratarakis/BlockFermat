def NonUnitalRingHom.toOpposite {R S : Type*} [NonUnitalNonAssocSemiring R]
    [NonUnitalNonAssocSemiring S] (f : R →ₙ+* S) (hf : ∀ x y, Commute (f x) (f y)) : R →ₙ+* Sᵐᵒᵖ :=
  { ((opAddEquiv : S ≃+ Sᵐᵒᵖ).toAddMonoidHom.comp ↑f : R →+ Sᵐᵒᵖ), f.toMulHom.toOpposite hf with
    toFun := MulOpposite.op ∘ f }
#align non_unital_ring_hom.to_opposite NonUnitalRingHom.toOpposite

def NonUnitalRingHom.fromOpposite {R S : Type*} [NonUnitalNonAssocSemiring R]
    [NonUnitalNonAssocSemiring S] (f : R →ₙ+* S) (hf : ∀ x y, Commute (f x) (f y)) : Rᵐᵒᵖ →ₙ+* S :=
  { (f.toAddMonoidHom.comp (opAddEquiv : R ≃+ Rᵐᵒᵖ).symm.toAddMonoidHom : Rᵐᵒᵖ →+ S),
    f.toMulHom.fromOpposite hf with toFun := f ∘ MulOpposite.unop }
#align non_unital_ring_hom.from_opposite NonUnitalRingHom.fromOpposite

def NonUnitalRingHom.op {α β} [NonUnitalNonAssocSemiring α] [NonUnitalNonAssocSemiring β] :
    (α →ₙ+* β) ≃ (αᵐᵒᵖ →ₙ+* βᵐᵒᵖ) where
  toFun f := { AddMonoidHom.mulOp f.toAddMonoidHom, MulHom.op f.toMulHom with }
  invFun f := { AddMonoidHom.mulUnop f.toAddMonoidHom, MulHom.unop f.toMulHom with }
  left_inv _ := rfl
  right_inv _ := rfl
#align non_unital_ring_hom.op NonUnitalRingHom.op

def NonUnitalRingHom.unop {α β} [NonUnitalNonAssocSemiring α] [NonUnitalNonAssocSemiring β] :
    (αᵐᵒᵖ →ₙ+* βᵐᵒᵖ) ≃ (α →ₙ+* β) :=
  NonUnitalRingHom.op.symm
#align non_unital_ring_hom.unop NonUnitalRingHom.unop

def RingHom.toOpposite {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S)
    (hf : ∀ x y, Commute (f x) (f y)) : R →+* Sᵐᵒᵖ :=
  { ((opAddEquiv : S ≃+ Sᵐᵒᵖ).toAddMonoidHom.comp ↑f : R →+ Sᵐᵒᵖ), f.toMonoidHom.toOpposite hf with
    toFun := MulOpposite.op ∘ f }
#align ring_hom.to_opposite RingHom.toOpposite

def RingHom.fromOpposite {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S)
    (hf : ∀ x y, Commute (f x) (f y)) : Rᵐᵒᵖ →+* S :=
  { (f.toAddMonoidHom.comp (opAddEquiv : R ≃+ Rᵐᵒᵖ).symm.toAddMonoidHom : Rᵐᵒᵖ →+ S),
    f.toMonoidHom.fromOpposite hf with toFun := f ∘ MulOpposite.unop }
#align ring_hom.from_opposite RingHom.fromOpposite

def RingHom.op {α β} [NonAssocSemiring α] [NonAssocSemiring β] :
    (α →+* β) ≃ (αᵐᵒᵖ →+* βᵐᵒᵖ) where
  toFun f := { AddMonoidHom.mulOp f.toAddMonoidHom, MonoidHom.op f.toMonoidHom with }
  invFun f := { AddMonoidHom.mulUnop f.toAddMonoidHom, MonoidHom.unop f.toMonoidHom with }
  left_inv _ := rfl
  right_inv _ := rfl
#align ring_hom.op RingHom.op

def RingHom.unop {α β} [NonAssocSemiring α] [NonAssocSemiring β] : (αᵐᵒᵖ →+* βᵐᵒᵖ) ≃ (α →+* β) :=
  RingHom.op.symm
#align ring_hom.unop RingHom.unop