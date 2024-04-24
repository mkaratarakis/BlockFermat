def A (f : E → F) (L : E →L[𝕜] F) (r ε : ℝ) : Set E :=
  { x | ∃ r' ∈ Ioc (r / 2) r, ∀ y ∈ ball x r', ∀ z ∈ ball x r', ‖f z - f y - L (z - y)‖ < ε * r }
#align fderiv_measurable_aux.A FDerivMeasurableAux.A

def B (f : E → F) (K : Set (E →L[𝕜] F)) (r s ε : ℝ) : Set E :=
  ⋃ L ∈ K, A f L r ε ∩ A f L s ε
#align fderiv_measurable_aux.B FDerivMeasurableAux.B

def D (f : E → F) (K : Set (E →L[𝕜] F)) : Set E :=
  ⋂ e : ℕ, ⋃ n : ℕ, ⋂ (p ≥ n) (q ≥ n), B f K ((1 / 2) ^ p) ((1 / 2) ^ q) ((1 / 2) ^ e)
#align fderiv_measurable_aux.D FDerivMeasurableAux.D

def A (f : ℝ → F) (L : F) (r ε : ℝ) : Set ℝ :=
  { x | ∃ r' ∈ Ioc (r / 2) r, ∀ᵉ (y ∈ Icc x (x + r')) (z ∈ Icc x (x + r')),
    ‖f z - f y - (z - y) • L‖ ≤ ε * r }
#align right_deriv_measurable_aux.A RightDerivMeasurableAux.A

def B (f : ℝ → F) (K : Set F) (r s ε : ℝ) : Set ℝ :=
  ⋃ L ∈ K, A f L r ε ∩ A f L s ε
#align right_deriv_measurable_aux.B RightDerivMeasurableAux.B

def D (f : ℝ → F) (K : Set F) : Set ℝ :=
  ⋂ e : ℕ, ⋃ n : ℕ, ⋂ (p ≥ n) (q ≥ n), B f K ((1 / 2) ^ p) ((1 / 2) ^ q) ((1 / 2) ^ e)
#align right_deriv_measurable_aux.D RightDerivMeasurableAux.D