def circleMap (c : ℂ) (R : ℝ) : ℝ → ℂ := fun θ => c + R * exp (θ * I)
#align circle_map circleMap

def CircleIntegrable (f : ℂ → E) (c : ℂ) (R : ℝ) : Prop :=
  IntervalIntegrable (fun θ : ℝ => f (circleMap c R θ)) volume 0 (2 * π)
#align circle_integrable CircleIntegrable

def circleIntegral (f : ℂ → E) (c : ℂ) (R : ℝ) : E :=
  ∫ θ : ℝ in (0)..2 * π, deriv (circleMap c R) θ • f (circleMap c R θ)
#align circle_integral circleIntegral

def {f : ℂ → E} {c : ℂ} {R : ℝ} (hf : ¬CircleIntegrable f c R) :
    (∮ z in C(c, R), f z) = 0 :=
  intervalIntegral.integral_undef (mt (circleIntegrable_iff R).mpr hf)
#align circle_integral.integral_undef circleIntegral.integral_undef

def hi
#align circle_integral.integral_eq_zero_of_has_deriv_within_at' circleIntegral.integral_eq_zero_of_hasDerivWithinAt'

def {n : ℤ} {c w : ℂ} {R : ℝ} (hn : n < 0)
    (hw : w ∈ sphere c |R|) : (∮ z in C(c, R), (z - w) ^ n) = 0 := by
  rcases eq_or_ne R 0 with (rfl | h0)
  · apply integral_radius_zero
  · apply integral_undef
    simpa [circleIntegrable_sub_zpow_iff, *, not_or]
#align circle_integral.integral_sub_zpow_of_undef circleIntegral.integral_sub_zpow_of_undef

def (hn.trans (by decide)) hw
  push_neg at H
  have hd : ∀ z, z ≠ w ∨ -1 ≤ n →
      HasDerivAt (fun z => (z - w) ^ (n + 1) / (n + 1)) ((z - w) ^ n) z := by
    intro z hne
    convert ((hasDerivAt_zpow (n + 1) _ (hne.imp _ _)).comp z
      ((hasDerivAt_id z).sub_const w)).div_const _ using 1
    · have hn' : (n + 1 : ℂ) ≠ 0 := by
        rwa [Ne, ← eq_neg_iff_add_eq_zero, ← Int.cast_one, ← Int.cast_neg, Int.cast_inj]
      simp [mul_assoc, mul_div_cancel_left₀ _ hn']
    exacts [sub_ne_zero.2, neg_le_iff_add_nonneg.1]
  refine' integral_eq_zero_of_hasDerivWithinAt' fun z hz => (hd z _).hasDerivWithinAt
  exact (ne_or_eq z w).imp_right fun (h : z = w) => H <| h ▸ hz
#align circle_integral.integral_sub_zpow_of_ne circleIntegral.integral_sub_zpow_of_ne

def cauchyPowerSeries (f : ℂ → E) (c : ℂ) (R : ℝ) : FormalMultilinearSeries ℂ ℂ E := fun n =>
  ContinuousMultilinearMap.mkPiRing ℂ _ <|
    (2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - c)⁻¹ ^ n • (z - c)⁻¹ • f z
#align cauchy_power_series cauchyPowerSeries