def Homeomorph.smul (γ : G) : α ≃ₜ α where
  toEquiv := MulAction.toPerm γ
  continuous_toFun := continuous_const_smul γ
  continuous_invFun := continuous_const_smul γ⁻¹
#align homeomorph.smul Homeomorph.smul

def Homeomorph.smulOfNeZero (c : G₀) (hc : c ≠ 0) : α ≃ₜ α :=
  Homeomorph.smul (Units.mk0 c hc)
#align homeomorph.smul_of_ne_zero Homeomorph.smulOfNeZero