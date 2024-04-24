def IsField.toSemifield {R : Type u} [Semiring R] (h : IsField R) : Semifield R :=
  { ‹Semiring R›, h with
    inv := fun a => if ha : a = 0 then 0 else Classical.choose (IsField.mul_inv_cancel h ha),
    inv_zero := dif_pos rfl,
    mul_inv_cancel := fun a ha => by
      convert Classical.choose_spec (IsField.mul_inv_cancel h ha)
      exact dif_neg ha }
#align is_field.to_semifield IsField.toSemifield

def IsField.toField {R : Type u} [Ring R] (h : IsField R) : Field R :=
  { ‹Ring R›, IsField.toSemifield h with qsmul := qsmulRec _ }
#align is_field.to_field IsField.toField

structure extends to a (semi)field. -/
structure IsField (R : Type u) [Semiring R] : Prop where
  /-- For a semiring to be a field, it must have two distinct elements. -/
  exists_pair_ne : ∃ x y : R, x ≠ y
  /-- Fields are commutative. -/
  mul_comm : ∀ x y : R, x * y = y * x
  /-- Nonzero elements have multiplicative inverses. -/
  mul_inv_cancel : ∀ {a : R}, a ≠ 0 → ∃ b, a * b = 1
#align is_field IsField