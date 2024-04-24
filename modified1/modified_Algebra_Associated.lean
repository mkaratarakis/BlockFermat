def Prime (p : α) : Prop :=
  p ≠ 0 ∧ ¬IsUnit p ∧ ∀ a b, p ∣ a * b → p ∣ a ∨ p ∣ b
#align prime Prime

def Associated [Monoid α] (x y : α) : Prop :=
  ∃ u : αˣ, x * u = y
#align associated Associated

def setoid (α : Type*) [Monoid α] :
    Setoid α where
  r := Associated
  iseqv := ⟨Associated.refl, Associated.symm, Associated.trans⟩
#align associated.setoid Associated.setoid

def mkMonoidHom : α →* Associates α where
  toFun := Associates.mk
  map_one' := mk_one
  map_mul' _ _ := mk_mul_mk
#align associates.mk_monoid_hom Associates.mkMonoidHom

structure Irreducible [Monoid α] (p : α) : Prop where
  /-- `p` is not a unit -/
  not_unit : ¬IsUnit p
  /-- if `p` factors then one factor is a unit -/
  isUnit_or_isUnit' : ∀ a b, p = a * b → IsUnit a ∨ IsUnit b
#align irreducible Irreducible

structure on `Associates α`. -/
abbrev Associates (α : Type*) [Monoid α] : Type _ :=
  Quotient (Associated.setoid α)
#align associates Associates