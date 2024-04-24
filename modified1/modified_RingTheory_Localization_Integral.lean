def coeffIntegerNormalization (p : S[X]) (i : ℕ) : R :=
  if hi : i ∈ p.support then
    Classical.choose
      (Classical.choose_spec (exist_integer_multiples_of_finset M (p.support.image p.coeff))
        (p.coeff i) (Finset.mem_image.mpr ⟨i, hi, rfl⟩))
  else 0
#align is_localization.coeff_integer_normalization IsLocalization.coeffIntegerNormalization

def integerNormalization (p : S[X]) : R[X] :=
  ∑ i in p.support, monomial i (coeffIntegerNormalization M p i)
#align is_localization.integer_normalization IsLocalization.integerNormalization