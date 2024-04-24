def zero_lt_one).mono fun n hn ↦ _⟩
    rwa [Real.norm_eq_abs, Real.norm_eq_abs, one_mul, abs_pow, abs_of_pos ha.1] at hn
  tfae_have 8 → 7
  exact fun ⟨a, ha, H⟩ ↦ ⟨a, ha.2, H⟩
  tfae_have 7 → 3
  · rintro ⟨a, ha, H⟩
    have : 0 ≤ a := nonneg_of_eventually_pow_nonneg (H.mono fun n ↦ (abs_nonneg _).trans)
    refine' ⟨a, A ⟨this, ha⟩, IsBigO.of_bound 1 _⟩
    simpa only [Real.norm_eq_abs, one_mul, abs_pow, abs_of_nonneg this]
  -- Porting note: used to work without explicitly having 6 → 7
  tfae_have 6 → 7
  · exact fun h ↦ tfae_8_to_7 <| tfae_2_to_8 <| tfae_3_to_2 <| tfae_5_to_3 <| tfae_6_to_5 h
  tfae_finish
#align tfae_exists_lt_is_o_pow TFAE_exists_lt_isLittleO_pow