def Simps.val_inv (u : αˣ) : α := ↑(u⁻¹)
#align units.simps.coe_inv Units.Simps.val_inv

def copy (u : αˣ) (val : α) (hv : val = u) (inv : α) (hi : inv = ↑u⁻¹) : αˣ :=
  { val, inv, inv_val := hv.symm ▸ hi.symm ▸ u.inv_val, val_inv := hv.symm ▸ hi.symm ▸ u.val_inv }
#align units.copy Units.copy

def Units.mkOfMulEqOne [CommMonoid α] (a b : α) (hab : a * b = 1) : αˣ :=
  ⟨a, b, hab, (mul_comm b a).trans hab⟩
#align units.mk_of_mul_eq_one Units.mkOfMulEqOne

def divp (a : α) (u : Units α) : α :=
  a * (u⁻¹ : αˣ)
#align divp divp

def IsUnit [Monoid M] (a : M) : Prop :=
  ∃ u : Mˣ, (u : M) = a
#align is_unit IsUnit

def unit (h : IsUnit a) : Mˣ :=
  (Classical.choose h).copy a (Classical.choose_spec h).symm _ rfl
#align is_unit.unit IsUnit.unit

def _root_.IsAddUnit.addUnit [AddMonoid N] {a : N} (h : IsAddUnit a) :
    AddUnits N :=
  (Classical.choose h).copy a (Classical.choose_spec h).symm _ rfl
#align is_add_unit.add_unit IsAddUnit.addUnit

def unit' (h : IsUnit a) : αˣ := ⟨a, a⁻¹, h.mul_inv_cancel, h.inv_mul_cancel⟩
#align is_unit.unit' IsUnit.unit'

def invOfIsUnit [Monoid M] (h : ∀ a : M, IsUnit a) : Inv M where
  inv := fun a => ↑(h a).unit⁻¹

/-- Constructs a `Group` structure on a `Monoid` consisting only of units. -/
noncomputable def groupOfIsUnit [hM : Monoid M] (h : ∀ a : M, IsUnit a) : Group M :=
  { hM with
    toInv := invOfIsUnit h,
    mul_left_inv := fun a => by
      change ↑(h a).unit⁻¹ * a = 1
      rw [Units.inv_mul_eq_iff_eq_mul, (h a).unit_spec, mul_one] }
#align group_of_is_unit groupOfIsUnit

def commGroupOfIsUnit [hM : CommMonoid M] (h : ∀ a : M, IsUnit a) : CommGroup M :=
  { hM with
    toInv := invOfIsUnit h,
    mul_left_inv := fun a => by
      change ↑(h a).unit⁻¹ * a = 1
      rw [Units.inv_mul_eq_iff_eq_mul, (h a).unit_spec, mul_one] }
#align comm_group_of_is_unit commGroupOfIsUnit

structure Units (α : Type u) [Monoid α] where
  /-- The underlying value in the base `Monoid`. -/
  val : α
  /-- The inverse value of `val` in the base `Monoid`. -/
  inv : α
  /-- `inv` is the right inverse of `val` in the base `Monoid`. -/
  val_inv : val * inv = 1
  /-- `inv` is the left inverse of `val` in the base `Monoid`. -/
  inv_val : inv * val = 1
#align units Units

structure AddUnits (α : Type u) [AddMonoid α] where
  /-- The underlying value in the base `AddMonoid`. -/
  val : α
  /-- The additive inverse value of `val` in the base `AddMonoid`. -/
  neg : α
  /-- `neg` is the right additive inverse of `val` in the base `AddMonoid`. -/
  val_neg : val + neg = 0
  /-- `neg` is the left additive inverse of `val` in the base `AddMonoid`. -/
  neg_val : neg + val = 0
#align add_units AddUnits

structure on a `Monoid` consisting only of units. -/
noncomputable def groupOfIsUnit [hM : Monoid M] (h : ∀ a : M, IsUnit a) : Group M :=
  { hM with
    toInv := invOfIsUnit h,
    mul_left_inv := fun a => by
      change ↑(h a).unit⁻¹ * a = 1
      rw [Units.inv_mul_eq_iff_eq_mul, (h a).unit_spec, mul_one] }
#align group_of_is_unit groupOfIsUnit

structure on a `CommMonoid` consisting only of units. -/
noncomputable def commGroupOfIsUnit [hM : CommMonoid M] (h : ∀ a : M, IsUnit a) : CommGroup M :=
  { hM with
    toInv := invOfIsUnit h,
    mul_left_inv := fun a => by
      change ↑(h a).unit⁻¹ * a = 1
      rw [Units.inv_mul_eq_iff_eq_mul, (h a).unit_spec, mul_one] }
#align comm_group_of_is_unit commGroupOfIsUnit