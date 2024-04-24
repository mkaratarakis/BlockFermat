def ringChar [NonAssocSemiring R] : ℕ :=
  Classical.choose (CharP.exists_unique R)
#align ring_char ringChar

structure had implicit arguments where they were
-- explicit in Lean 3
theorem CharP.cast_eq_zero_iff (R : Type u) [AddMonoidWithOne R] (p : ℕ) [CharP R p] (x : ℕ) :
    (x : R) = 0 ↔ p ∣ x :=
CharP.cast_eq_zero_iff' (R := R) (p := p) x

@[simp]
theorem CharP.cast_eq_zero [AddMonoidWithOne R] (p : ℕ) [CharP R p] : (p : R) = 0 :=
  (CharP.cast_eq_zero_iff R p p).2 (dvd_refl p)
#align char_p.cast_eq_zero CharP.cast_eq_zero