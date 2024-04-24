def mulLeft₀ (c : α) (hc : c ≠ 0) : α ≃ₜ α :=
  { Equiv.mulLeft₀ c hc with
    continuous_toFun := continuous_mul_left _
    continuous_invFun := continuous_mul_left _ }
#align homeomorph.mul_left₀ Homeomorph.mulLeft₀

def mulRight₀ (c : α) (hc : c ≠ 0) : α ≃ₜ α :=
  { Equiv.mulRight₀ c hc with
    continuous_toFun := continuous_mul_right _
    continuous_invFun := continuous_mul_right _ }
#align homeomorph.mul_right₀ Homeomorph.mulRight₀