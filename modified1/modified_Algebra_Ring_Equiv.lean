def NonUnitalRingHom.inverse
    [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S]
    (f : R →ₙ+* S) (g : S → R)
    (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) : S →ₙ+* R :=
  { (f : R →+ S).inverse g h₁ h₂, (f : R →ₙ* S).inverse g h₁ h₂ with toFun := g }

/-- makes a `RingHom` from the bijective inverse of a `RingHom` -/
@[simps] def RingHom.inverse [NonAssocSemiring R] [NonAssocSemiring S]
    (f : RingHom R S) (g : S → R)
    (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) : S →+* R :=
  { (f : OneHom R S).inverse g h₁,
    (f : MulHom R S).inverse g h₁ h₂,
    (f : R →+ S).inverse g h₁ h₂ with toFun := g }

/-- An equivalence between two (non-unital non-associative semi)rings that preserves the
algebraic structure. -/
structure RingEquiv (R S : Type*) [Mul R] [Mul S] [Add R] [Add S] extends R ≃ S, R ≃* S, R ≃+ S
#align ring_equiv RingEquiv

def toRingEquiv [Mul α] [Add α] [Mul β] [Add β] [EquivLike F α β] [RingEquivClass F α β] (f : F) :
    α ≃+* β :=
  { (f : α ≃* β), (f : α ≃+ β) with }

end RingEquivClass

/-- Any type satisfying `RingEquivClass` can be cast into `RingEquiv` via
`RingEquivClass.toRingEquiv`. -/
instance [Mul α] [Add α] [Mul β] [Add β] [EquivLike F α β] [RingEquivClass F α β] :
    CoeTC F (α ≃+* β) :=
  ⟨RingEquivClass.toRingEquiv⟩

namespace RingEquiv

section Basic

variable [Mul R] [Mul S] [Add R] [Add S] [Mul S'] [Add S']

instance : EquivLike (R ≃+* S) R S where
  coe f := f.toFun
  inv f := f.invFun
  coe_injective' e f h₁ h₂ := by
    cases e
    cases f
    congr
    apply Equiv.coe_fn_injective h₁
  left_inv f := f.left_inv
  right_inv f := f.right_inv

instance : RingEquivClass (R ≃+* S) R S where
  map_add f := f.map_add'
  map_mul f := f.map_mul'

@[simp]
theorem toEquiv_eq_coe (f : R ≃+* S) : f.toEquiv = f :=
  rfl
#align ring_equiv.to_equiv_eq_coe RingEquiv.toEquiv_eq_coe

def ringEquivOfUnique {M N} [Unique M] [Unique N] [Add M] [Mul M] [Add N] [Mul N] : M ≃+* N :=
  { AddEquiv.addEquivOfUnique, MulEquiv.mulEquivOfUnique with }
#align ring_equiv.ring_equiv_of_unique RingEquiv.ringEquivOfUnique

def refl : R ≃+* R :=
  { MulEquiv.refl R, AddEquiv.refl R with }
#align ring_equiv.refl RingEquiv.refl

def symm (e : R ≃+* S) : S ≃+* R :=
  { e.toMulEquiv.symm, e.toAddEquiv.symm with }
#align ring_equiv.symm RingEquiv.symm

def Simps.symm_apply (e : R ≃+* S) : S → R :=
  e.symm
#align ring_equiv.simps.symm_apply RingEquiv.Simps.symm_apply

def trans (e₁ : R ≃+* S) (e₂ : S ≃+* S') : R ≃+* S' :=
  { e₁.toMulEquiv.trans e₂.toMulEquiv, e₁.toAddEquiv.trans e₂.toAddEquiv with }
#align ring_equiv.trans RingEquiv.trans

def op {α β} [Add α] [Mul α] [Add β] [Mul β] :
    α ≃+* β ≃ (αᵐᵒᵖ ≃+* βᵐᵒᵖ) where
  toFun f := { AddEquiv.mulOp f.toAddEquiv, MulEquiv.op f.toMulEquiv with }
  invFun f := { AddEquiv.mulOp.symm f.toAddEquiv, MulEquiv.op.symm f.toMulEquiv with }
  left_inv f := by
    ext
    rfl
  right_inv f := by
    ext
    rfl
#align ring_equiv.op RingEquiv.op

def unop {α β} [Add α] [Mul α] [Add β] [Mul β] : αᵐᵒᵖ ≃+* βᵐᵒᵖ ≃ (α ≃+* β) :=
  RingEquiv.op.symm
#align ring_equiv.unop RingEquiv.unop

def opOp (R : Type*) [Add R] [Mul R] : R ≃+* Rᵐᵒᵖᵐᵒᵖ where
  __ := MulEquiv.opOp R
  map_add' _ _ := rfl

section NonUnitalCommSemiring

variable (R) [NonUnitalCommSemiring R]

/-- A non-unital commutative ring is isomorphic to its opposite. -/
def toOpposite : R ≃+* Rᵐᵒᵖ :=
  { MulOpposite.opEquiv with
    map_add' := fun _ _ => rfl
    map_mul' := fun x y => mul_comm (op y) (op x) }
#align ring_equiv.to_opposite RingEquiv.toOpposite

def ofBijective [NonUnitalRingHomClass F R S] (f : F) (hf : Function.Bijective f) :
    R ≃+* S :=
  { Equiv.ofBijective f hf with
    map_mul' := map_mul f
    map_add' := map_add f }
#align ring_equiv.of_bijective RingEquiv.ofBijective

def piCongrRight {ι : Type*} {R S : ι → Type*} [∀ i, NonUnitalNonAssocSemiring (R i)]
    [∀ i, NonUnitalNonAssocSemiring (S i)] (e : ∀ i, R i ≃+* S i) : (∀ i, R i) ≃+* ∀ i, S i :=
  { @MulEquiv.piCongrRight ι R S _ _ fun i => (e i).toMulEquiv,
    @AddEquiv.piCongrRight ι R S _ _ fun i => (e i).toAddEquiv with
    toFun := fun x j => e j (x j)
    invFun := fun x j => (e j).symm (x j) }
#align ring_equiv.Pi_congr_right RingEquiv.piCongrRight

def toNonUnitalRingHom (e : R ≃+* S) : R →ₙ+* S :=
  { e.toMulEquiv.toMulHom, e.toAddEquiv.toAddMonoidHom with }
#align ring_equiv.to_non_unital_ring_hom RingEquiv.toNonUnitalRingHom

def toRingHom (e : R ≃+* S) : R →+* S :=
  { e.toMulEquiv.toMonoidHom, e.toAddEquiv.toAddMonoidHom with }
#align ring_equiv.to_ring_hom RingEquiv.toRingHom

def ofHomInv' {R S F G : Type*} [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S]
    [FunLike F R S] [FunLike G S R]
    [NonUnitalRingHomClass F R S] [NonUnitalRingHomClass G S R] (hom : F) (inv : G)
    (hom_inv_id : (inv : S →ₙ+* R).comp (hom : R →ₙ+* S) = NonUnitalRingHom.id R)
    (inv_hom_id : (hom : R →ₙ+* S).comp (inv : S →ₙ+* R) = NonUnitalRingHom.id S) :
    R ≃+* S where
  toFun := hom
  invFun := inv
  left_inv := DFunLike.congr_fun hom_inv_id
  right_inv := DFunLike.congr_fun inv_hom_id
  map_mul' := map_mul hom
  map_add' := map_add hom
#align ring_equiv.of_hom_inv' RingEquiv.ofHomInv'

def ofHomInv {R S F G : Type*} [NonAssocSemiring R] [NonAssocSemiring S]
    [FunLike F R S] [FunLike G S R] [RingHomClass F R S]
    [RingHomClass G S R] (hom : F) (inv : G)
    (hom_inv_id : (inv : S →+* R).comp (hom : R →+* S) = RingHom.id R)
    (inv_hom_id : (hom : R →+* S).comp (inv : S →+* R) = RingHom.id S) :
    R ≃+* S where
  toFun := hom
  invFun := inv
  left_inv := DFunLike.congr_fun hom_inv_id
  right_inv := DFunLike.congr_fun inv_hom_id
  map_mul' := map_mul hom
  map_add' := map_add hom
#align ring_equiv.of_hom_inv RingEquiv.ofHomInv

def toRingEquiv {R S F : Type*} [Add R] [Add S] [Mul R] [Mul S] [EquivLike F R S]
    [MulEquivClass F R S] (f : F)
    (H : ∀ x y : R, f (x + y) = f x + f y) : R ≃+* S :=
  { (f : R ≃* S).toEquiv, (f : R ≃* S), AddEquiv.mk' (f : R ≃* S).toEquiv H with }
#align mul_equiv.to_ring_equiv MulEquiv.toRingEquiv

def toRingEquiv {R S F : Type*} [Add R] [Add S] [Mul R] [Mul S] [EquivLike F R S]
    [AddEquivClass F R S] (f : F)
    (H : ∀ x y : R, f (x * y) = f x * f y) : R ≃+* S :=
  { (f : R ≃+ S).toEquiv, (f : R ≃+ S), MulEquiv.mk' (f : R ≃+ S).toEquiv H with }
#align add_equiv.to_ring_equiv AddEquiv.toRingEquiv

structure RingEquiv (R S : Type*) [Mul R] [Mul S] [Add R] [Add S] extends R ≃ S, R ≃* S, R ≃+ S
#align ring_equiv RingEquiv

structure preserving equivalences.
You should extend this class when you extend `RingEquiv`. -/
class RingEquivClass (F R S : Type*) [Mul R] [Add R] [Mul S] [Add S] [EquivLike F R S]
  extends MulEquivClass F R S : Prop where
  /-- By definition, a ring isomorphism preserves the additive structure. -/
  map_add : ∀ (f : F) (a b), f (a + b) = f a + f b
#align ring_equiv_class RingEquivClass