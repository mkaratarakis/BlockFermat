def fixingSubmonoid (s : Set α) : Submonoid M
    where
  carrier := { ϕ : M | ∀ x : s, ϕ • (x : α) = x }
  one_mem' _ := one_smul _ _
  mul_mem' {x y} hx hy z := by rw [mul_smul, hy z, hx z]
#align fixing_submonoid fixingSubmonoid

def fixingSubgroup (s : Set α) : Subgroup M :=
  { fixingSubmonoid M s with inv_mem' := fun hx z => by rw [inv_smul_eq_iff, hx z] }
#align fixing_subgroup fixingSubgroup