def IntervalIntegrable (f : ℝ → E) (μ : Measure ℝ) (a b : ℝ) : Prop :=
  IntegrableOn f (Ioc a b) μ ∧ IntegrableOn f (Ioc b a) μ
#align interval_integrable IntervalIntegrable

def IntervalIntegrable.def'

theorem intervalIntegrable_iff_integrableOn_Ioc_of_le (hab : a ≤ b) :
    IntervalIntegrable f μ a b ↔ IntegrableOn f (Ioc a b) μ := by
  rw [intervalIntegrable_iff, uIoc_of_le hab]
#align interval_integrable_iff_integrable_Ioc_of_le intervalIntegrable_iff_integrableOn_Ioc_of_le

def intervalIntegral (f : ℝ → E) (a b : ℝ) (μ : Measure ℝ) : E :=
  (∫ x in Ioc a b, f x ∂μ) - ∫ x in Ioc b a, f x ∂μ
#align interval_integral intervalIntegral

def (h : ¬IntervalIntegrable f μ a b) : ∫ x in a..b, f x ∂μ = 0 := by
  rw [intervalIntegrable_iff] at h
  rw [intervalIntegral_eq_integral_uIoc, integral_undef h, smul_zero]
#align interval_integral.integral_undef intervalIntegral.integral_undef

def h
#align interval_integral.interval_integrable_of_integral_ne_zero intervalIntegral.intervalIntegrable_of_integral_ne_zero