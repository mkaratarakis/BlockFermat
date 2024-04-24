def HasFiniteIntegral {_ : MeasurableSpace α} (f : α → β) (μ : Measure α := by volume_tac) : Prop :=
  (∫⁻ a, ‖f a‖₊ ∂μ) < ∞
#align measure_theory.has_finite_integral MeasureTheory.HasFiniteIntegral

def {_ : MeasurableSpace α} (f : α → β) (μ : Measure α) :
    HasFiniteIntegral f μ ↔ ((∫⁻ a, ‖f a‖₊ ∂μ) < ∞) :=
  Iff.rfl

theorem hasFiniteIntegral_iff_norm (f : α → β) :
    HasFiniteIntegral f μ ↔ (∫⁻ a, ENNReal.ofReal ‖f a‖ ∂μ) < ∞ := by
  simp only [HasFiniteIntegral, ofReal_norm_eq_coe_nnnorm]
#align measure_theory.has_finite_integral_iff_norm MeasureTheory.hasFiniteIntegral_iff_norm

def Integrable {α} {_ : MeasurableSpace α} (f : α → β) (μ : Measure α := by volume_tac) : Prop :=
  AEStronglyMeasurable f μ ∧ HasFiniteIntegral f μ
#align measure_theory.integrable MeasureTheory.Integrable

def withDensitySMulLI {f : α → ℝ≥0} (f_meas : Measurable f) :
    Lp E 1 (μ.withDensity fun x => f x) →ₗᵢ[ℝ] Lp E 1 μ where
  toFun u := (memℒ1_smul_of_L1_withDensity f_meas u).toLp _
  map_add' := by
    intro u v
    ext1
    filter_upwards [(memℒ1_smul_of_L1_withDensity f_meas u).coeFn_toLp,
      (memℒ1_smul_of_L1_withDensity f_meas v).coeFn_toLp,
      (memℒ1_smul_of_L1_withDensity f_meas (u + v)).coeFn_toLp,
      Lp.coeFn_add ((memℒ1_smul_of_L1_withDensity f_meas u).toLp _)
        ((memℒ1_smul_of_L1_withDensity f_meas v).toLp _),
      (ae_withDensity_iff f_meas.coe_nnreal_ennreal).1 (Lp.coeFn_add u v)]
    intro x hu hv huv h' h''
    rw [huv, h', Pi.add_apply, hu, hv]
    rcases eq_or_ne (f x) 0 with (hx | hx)
    · simp only [hx, zero_smul, add_zero]
    · rw [h'' _, Pi.add_apply, smul_add]
      simpa only [Ne, ENNReal.coe_eq_zero] using hx
  map_smul' := by
    intro r u
    ext1
    filter_upwards [(ae_withDensity_iff f_meas.coe_nnreal_ennreal).1 (Lp.coeFn_smul r u),
      (memℒ1_smul_of_L1_withDensity f_meas (r • u)).coeFn_toLp,
      Lp.coeFn_smul r ((memℒ1_smul_of_L1_withDensity f_meas u).toLp _),
      (memℒ1_smul_of_L1_withDensity f_meas u).coeFn_toLp]
    intro x h h' h'' h'''
    rw [RingHom.id_apply, h', h'', Pi.smul_apply, h''']
    rcases eq_or_ne (f x) 0 with (hx | hx)
    · simp only [hx, zero_smul, smul_zero]
    · rw [h _, smul_comm, Pi.smul_apply]
      simpa only [Ne, ENNReal.coe_eq_zero] using hx
  norm_map' := by
    intro u
    -- Porting note: Lean can't infer types of `AddHom.coe_mk`.
    simp only [snorm, LinearMap.coe_mk,
      AddHom.coe_mk (M := Lp E 1 (μ.withDensity fun x => f x)) (N := Lp E 1 μ), Lp.norm_toLp,
      one_ne_zero, ENNReal.one_ne_top, ENNReal.one_toReal, if_false, snorm', ENNReal.rpow_one,
      _root_.div_one, Lp.norm_def]
    rw [lintegral_withDensity_eq_lintegral_mul_non_measurable _ f_meas.coe_nnreal_ennreal
        (Filter.eventually_of_forall fun x => ENNReal.coe_lt_top)]
    congr 1
    apply lintegral_congr_ae
    filter_upwards [(memℒ1_smul_of_L1_withDensity f_meas u).coeFn_toLp] with x hx
    rw [hx, Pi.mul_apply]
    change (‖(f x : ℝ) • u x‖₊ : ℝ≥0∞) = (f x : ℝ≥0∞) * (‖u x‖₊ : ℝ≥0∞)
    simp only [nnnorm_smul, NNReal.nnnorm_eq, ENNReal.coe_mul]
#align measure_theory.with_density_smul_li MeasureTheory.withDensitySMulLI

def Integrable (f : α →ₘ[μ] β) : Prop :=
  MeasureTheory.Integrable f μ
#align measure_theory.ae_eq_fun.integrable MeasureTheory.AEEqFun.Integrable

def (f g : α →₁[μ] β) : edist f g = ∫⁻ a, edist (f a) (g a) ∂μ := by
  simp only [Lp.edist_def, snorm, one_ne_zero, snorm', Pi.sub_apply, one_toReal, ENNReal.rpow_one,
    ne_eq, not_false_eq_true, div_self, ite_false]
  simp [edist_eq_coe_nnnorm_sub]
#align measure_theory.L1.edist_def MeasureTheory.L1.edist_def

def (f g : α →₁[μ] β) : dist f g = (∫⁻ a, edist (f a) (g a) ∂μ).toReal := by
  simp only [Lp.dist_def, snorm, one_ne_zero, snorm', Pi.sub_apply, one_toReal, ENNReal.rpow_one,
    ne_eq, not_false_eq_true, div_self, ite_false]
  simp [edist_eq_coe_nnnorm_sub]
#align measure_theory.L1.dist_def MeasureTheory.L1.dist_def

def (f : α →₁[μ] β) : ‖f‖ = (∫⁻ a, ‖f a‖₊ ∂μ).toReal := by
  simp [Lp.norm_def, snorm, snorm']
#align measure_theory.L1.norm_def MeasureTheory.L1.norm_def

def toL1 (f : α → β) (hf : Integrable f μ) : α →₁[μ] β :=
  (memℒp_one_iff_integrable.2 hf).toLp f
#align measure_theory.integrable.to_L1 MeasureTheory.Integrable.toL1