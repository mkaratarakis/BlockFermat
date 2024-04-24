def ValueGroup : Type v := Quotient (MulAction.orbitRel Aˣ K)
#align valuation_ring.value_group ValuationRing.ValueGroup

def valuation : Valuation K (ValueGroup A K) where
  toFun := Quotient.mk''
  map_zero' := rfl
  map_one' := rfl
  map_mul' _ _ := rfl
  map_add_le_max' := by
    intro a b
    obtain ⟨xa, ya, hya, rfl⟩ : ∃ a b : A, _ := IsFractionRing.div_surjective a
    obtain ⟨xb, yb, hyb, rfl⟩ : ∃ a b : A, _ := IsFractionRing.div_surjective b
    have : (algebraMap A K) ya ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hya
    have : (algebraMap A K) yb ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hyb
    obtain ⟨c, h | h⟩ := ValuationRing.cond (xa * yb) (xb * ya)
    dsimp
    · apply le_trans _ (le_max_left _ _)
      use c + 1
      rw [Algebra.smul_def]
      field_simp
      simp only [← RingHom.map_mul, ← RingHom.map_add, ← (algebraMap A K).map_one, ← h]
      congr 1; ring
    · apply le_trans _ (le_max_right _ _)
      use c + 1
      rw [Algebra.smul_def]
      field_simp
      simp only [← RingHom.map_mul, ← RingHom.map_add, ← (algebraMap A K).map_one, ← h]
      congr 1; ring
#align valuation_ring.valuation ValuationRing.valuation

def equivInteger : A ≃+* (valuation A K).integer :=
  RingEquiv.ofBijective
    (show A →ₙ+* (valuation A K).integer from
      { toFun := fun a => ⟨algebraMap A K a, (mem_integer_iff _ _ _).mpr ⟨a, rfl⟩⟩
        map_mul' := fun _ _ => by ext1; exact (algebraMap A K).map_mul _ _
        map_zero' := by ext1; exact (algebraMap A K).map_zero
        map_add' := fun _ _ => by ext1; exact (algebraMap A K).map_add _ _ })
    (by
      constructor
      · intro x y h
        apply_fun (algebraMap (valuation A K).integer K) at h
        exact IsFractionRing.injective _ _ h
      · rintro ⟨-, ha⟩
        rw [mem_integer_iff] at ha
        obtain ⟨a, rfl⟩ := ha
        exact ⟨a, rfl⟩)
#align valuation_ring.equiv_integer ValuationRing.equivInteger