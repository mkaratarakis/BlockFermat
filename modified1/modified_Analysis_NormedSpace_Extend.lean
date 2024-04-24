def extendTo𝕜' (fr : F →ₗ[ℝ] ℝ) : F →ₗ[𝕜] 𝕜 := by
  let fc : F → 𝕜 := fun x => (fr x : 𝕜) - (I : 𝕜) * fr ((I : 𝕜) • x)
  have add : ∀ x y : F, fc (x + y) = fc x + fc y := by
    intro x y
    simp only [fc, smul_add, LinearMap.map_add, ofReal_add]
    rw [mul_add]
    abel
  have A : ∀ (c : ℝ) (x : F), (fr ((c : 𝕜) • x) : 𝕜) = (c : 𝕜) * (fr x : 𝕜) := by
    intro c x
    rw [← ofReal_mul]
    congr 1
    rw [RCLike.ofReal_alg, smul_assoc, fr.map_smul, Algebra.id.smul_eq_mul, one_smul]
  have smul_ℝ : ∀ (c : ℝ) (x : F), fc ((c : 𝕜) • x) = (c : 𝕜) * fc x := by
    intro c x
    dsimp only [fc]
    rw [A c x, smul_smul, mul_comm I (c : 𝕜), ← smul_smul, A, mul_sub]
    ring
  have smul_I : ∀ x : F, fc ((I : 𝕜) • x) = (I : 𝕜) * fc x := by
    intro x
    dsimp only [fc]
    cases' @I_mul_I_ax 𝕜 _ with h h
    · simp [h]
    rw [mul_sub, ← mul_assoc, smul_smul, h]
    simp only [neg_mul, LinearMap.map_neg, one_mul, one_smul, mul_neg, ofReal_neg, neg_smul,
      sub_neg_eq_add, add_comm]
  have smul_𝕜 : ∀ (c : 𝕜) (x : F), fc (c • x) = c • fc x := by
    intro c x
    rw [← re_add_im c, add_smul, add_smul, add, smul_ℝ, ← smul_smul, smul_ℝ, smul_I, ← mul_assoc]
    rfl
  exact
    { toFun := fc
      map_add' := add
      map_smul' := smul_𝕜 }
#align linear_map.extend_to_𝕜' LinearMap.extendTo𝕜'

def extendTo𝕜' (fr : F →L[ℝ] ℝ) : F →L[𝕜] 𝕜 :=
  LinearMap.mkContinuous _ ‖fr‖ fr.norm_extendTo𝕜'_bound
#align continuous_linear_map.extend_to_𝕜' ContinuousLinearMap.extendTo𝕜'

def LinearMap.extendTo𝕜 (fr : RestrictScalars ℝ 𝕜 F →ₗ[ℝ] ℝ) : F →ₗ[𝕜] 𝕜 :=
  fr.extendTo𝕜'
#align linear_map.extend_to_𝕜 LinearMap.extendTo𝕜

def ContinuousLinearMap.extendTo𝕜 (fr : RestrictScalars ℝ 𝕜 F →L[ℝ] ℝ) : F →L[𝕜] 𝕜 :=
  fr.extendTo𝕜'
#align continuous_linear_map.extend_to_𝕜 ContinuousLinearMap.extendTo𝕜