def invertibleOfRingCharNotDvd {t : ℕ} (not_dvd : ¬ringChar K ∣ t) : Invertible (t : K) :=
  invertibleOfNonzero fun h => not_dvd ((ringChar.spec K t).mp h)
#align invertible_of_ring_char_not_dvd invertibleOfRingCharNotDvd

def invertibleOfCharPNotDvd {p : ℕ} [CharP K p] {t : ℕ} (not_dvd : ¬p ∣ t) : Invertible (t : K) :=
  invertibleOfNonzero fun h => not_dvd ((CharP.cast_eq_zero_iff K p t).mp h)
#align invertible_of_char_p_not_dvd invertibleOfCharPNotDvd