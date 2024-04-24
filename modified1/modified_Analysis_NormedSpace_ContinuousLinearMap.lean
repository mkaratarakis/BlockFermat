def LinearMap.mkContinuous (C : ℝ) (h : ∀ x, ‖f x‖ ≤ C * ‖x‖) : E →SL[σ] F :=
  ⟨f, AddMonoidHomClass.continuous_of_bound f C h⟩
#align linear_map.mk_continuous LinearMap.mkContinuous

def LinearMap.mkContinuousOfExistsBound (h : ∃ C, ∀ x, ‖f x‖ ≤ C * ‖x‖) : E →SL[σ] F :=
  ⟨f,
    let ⟨C, hC⟩ := h
    AddMonoidHomClass.continuous_of_bound f C hC⟩
#align linear_map.mk_continuous_of_exists_bound LinearMap.mkContinuousOfExistsBound

def LinearEquiv.toContinuousLinearEquivOfBounds (e : E ≃ₛₗ[σ] F) (C_to C_inv : ℝ)
    (h_to : ∀ x, ‖e x‖ ≤ C_to * ‖x‖) (h_inv : ∀ x : F, ‖e.symm x‖ ≤ C_inv * ‖x‖) : E ≃SL[σ] F where
  toLinearEquiv := e
  continuous_toFun := AddMonoidHomClass.continuous_of_bound e C_to h_to
  continuous_invFun := AddMonoidHomClass.continuous_of_bound e.symm C_inv h_inv
#align linear_equiv.to_continuous_linear_equiv_of_bounds LinearEquiv.toContinuousLinearEquivOfBounds

def LinearMap.toContinuousLinearMap₁ (f : 𝕜 →ₗ[𝕜] E) : 𝕜 →L[𝕜] E :=
  f.mkContinuous ‖f 1‖ fun x => by
    conv_lhs => rw [← mul_one x]
    rw [← smul_eq_mul, f.map_smul, mul_comm]; exact norm_smul_le _ _
#align linear_map.to_continuous_linear_map₁ LinearMap.toContinuousLinearMap₁

def ContinuousLinearMap.ofHomothety (f : E →ₛₗ[σ] F) (a : ℝ) (hf : ∀ x, ‖f x‖ = a * ‖x‖) :
    E →SL[σ] F :=
  f.mkContinuous a fun x => le_of_eq (hf x)
#align continuous_linear_map.of_homothety ContinuousLinearMap.ofHomothety

def ContinuousLinearEquiv.ofHomothety (f : E ≃ₛₗ[σ] F) (a : ℝ) (ha : 0 < a)
    (hf : ∀ x, ‖f x‖ = a * ‖x‖) : E ≃SL[σ] F :=
  LinearEquiv.toContinuousLinearEquivOfBounds f a a⁻¹ (fun x => (hf x).le) fun x =>
    (ContinuousLinearEquiv.homothety_inverse a ha f hf x).le
#align continuous_linear_equiv.of_homothety ContinuousLinearEquiv.ofHomothety