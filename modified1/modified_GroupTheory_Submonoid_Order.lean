def oneLE : Submonoid M where
  carrier := Set.Ici 1
  mul_mem' := one_le_mul
  one_mem' := le_rfl

variable {M}

@[to_additive (attr := simp) mem_nonneg] lemma mem_oneLE : a ∈ oneLE M ↔ 1 ≤ a := Iff.rfl

end Preorder

section MulZeroClass
variable (α) [MulZeroOneClass α] [PartialOrder α] [PosMulStrictMono α] [ZeroLEOneClass α]
  [NeZero (1 : α)] {a : α}

/-- The submonoid of positive elements. -/
@[simps] def pos : Submonoid α where
  carrier := Set.Ioi 0
  one_mem' := zero_lt_one
  mul_mem' := mul_pos
#align pos_submonoid Submonoid.pos