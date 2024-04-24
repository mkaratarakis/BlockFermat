def arcsin : ℝ → ℝ :=
  Subtype.val ∘ IccExtend (neg_le_self zero_le_one) sinOrderIso.symm
#align real.arcsin Real.arcsin

def sinPartialHomeomorph : PartialHomeomorph ℝ ℝ where
  toFun := sin
  invFun := arcsin
  source := Ioo (-(π / 2)) (π / 2)
  target := Ioo (-1) 1
  map_source' := mapsTo_sin_Ioo
  map_target' _ hy := ⟨neg_pi_div_two_lt_arcsin.2 hy.1, arcsin_lt_pi_div_two.2 hy.2⟩
  left_inv' _ hx := arcsin_sin hx.1.le hx.2.le
  right_inv' _ hy := sin_arcsin hy.1.le hy.2.le
  open_source := isOpen_Ioo
  open_target := isOpen_Ioo
  continuousOn_toFun := continuous_sin.continuousOn
  continuousOn_invFun := continuous_arcsin.continuousOn
#align real.sin_local_homeomorph Real.sinPartialHomeomorph

def arccos (x : ℝ) : ℝ :=
  π / 2 - arcsin x
#align real.arccos Real.arccos