def inverse : M₀ → M₀ := fun x => if h : IsUnit x then ((h.unit⁻¹ : M₀ˣ) : M₀) else 0
#align ring.inverse Ring.inverse

def mk0 (a : G₀) (ha : a ≠ 0) : G₀ˣ :=
  ⟨a, a⁻¹, mul_inv_cancel ha, inv_mul_cancel ha⟩
#align units.mk0 Units.mk0

def groupWithZeroOfIsUnitOrEqZero [hM : MonoidWithZero M]
    (h : ∀ a : M, IsUnit a ∨ a = 0) : GroupWithZero M :=
  { hM with
    inv := fun a => if h0 : a = 0 then 0 else ↑((h a).resolve_right h0).unit⁻¹,
    inv_zero := dif_pos rfl,
    mul_inv_cancel := fun a h0 => by
      change (a * if h0 : a = 0 then 0 else ↑((h a).resolve_right h0).unit⁻¹) = 1
      rw [dif_neg h0, Units.mul_inv_eq_iff_eq_mul, one_mul, IsUnit.unit_spec],
    exists_pair_ne := Nontrivial.exists_pair_ne }
#align group_with_zero_of_is_unit_or_eq_zero groupWithZeroOfIsUnitOrEqZero

def commGroupWithZeroOfIsUnitOrEqZero [hM : CommMonoidWithZero M]
    (h : ∀ a : M, IsUnit a ∨ a = 0) : CommGroupWithZero M :=
  { groupWithZeroOfIsUnitOrEqZero h, hM with }
#align comm_group_with_zero_of_is_unit_or_eq_zero commGroupWithZeroOfIsUnitOrEqZero

structure on a `MonoidWithZero`
  consisting only of units and 0. -/
noncomputable def groupWithZeroOfIsUnitOrEqZero [hM : MonoidWithZero M]
    (h : ∀ a : M, IsUnit a ∨ a = 0) : GroupWithZero M :=
  { hM with
    inv := fun a => if h0 : a = 0 then 0 else ↑((h a).resolve_right h0).unit⁻¹,
    inv_zero := dif_pos rfl,
    mul_inv_cancel := fun a h0 => by
      change (a * if h0 : a = 0 then 0 else ↑((h a).resolve_right h0).unit⁻¹) = 1
      rw [dif_neg h0, Units.mul_inv_eq_iff_eq_mul, one_mul, IsUnit.unit_spec],
    exists_pair_ne := Nontrivial.exists_pair_ne }
#align group_with_zero_of_is_unit_or_eq_zero groupWithZeroOfIsUnitOrEqZero

structure on a `CommMonoidWithZero`
  consisting only of units and 0. -/
noncomputable def commGroupWithZeroOfIsUnitOrEqZero [hM : CommMonoidWithZero M]
    (h : ∀ a : M, IsUnit a ∨ a = 0) : CommGroupWithZero M :=
  { groupWithZeroOfIsUnitOrEqZero h, hM with }
#align comm_group_with_zero_of_is_unit_or_eq_zero commGroupWithZeroOfIsUnitOrEqZero