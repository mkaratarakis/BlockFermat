def integer : Subring R where
  carrier := { x | v x ≤ 1 }
  one_mem' := le_of_eq v.map_one
  mul_mem' {x y} hx hy := by simp only [Set.mem_setOf_eq, _root_.map_mul, mul_le_one' hx hy]
  zero_mem' := by simp only [Set.mem_setOf_eq, _root_.map_zero, zero_le']
  add_mem' {x y} hx hy := le_trans (v.map_add x y) (max_le hx hy)
  neg_mem' {x} hx := by simp only [Set.mem_setOf_eq] at hx; simpa only [Set.mem_setOf_eq, map_neg]
#align valuation.integer Valuation.integer

structure Integers : Prop where
  hom_inj : Function.Injective (algebraMap O R)
  map_le_one : ∀ x, v (algebraMap O R x) ≤ 1
  exists_of_le_one : ∀ ⦃r⦄, v r ≤ 1 → ∃ x, algebraMap O R x = r
#align valuation.integers Valuation.Integers