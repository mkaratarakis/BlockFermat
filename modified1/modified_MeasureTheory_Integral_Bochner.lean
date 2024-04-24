def weightedSMul {_ : MeasurableSpace α} (μ : Measure α) (s : Set α) : F →L[ℝ] F :=
  (μ s).toReal • ContinuousLinearMap.id ℝ F
#align measure_theory.weighted_smul MeasureTheory.weightedSMul

def posPart (f : α →ₛ E) : α →ₛ E :=
  f.map fun b => max b 0
#align measure_theory.simple_func.pos_part MeasureTheory.SimpleFunc.posPart

def negPart [Neg E] (f : α →ₛ E) : α →ₛ E :=
  posPart (-f)
#align measure_theory.simple_func.neg_part MeasureTheory.SimpleFunc.negPart

def integral {_ : MeasurableSpace α} (μ : Measure α) (f : α →ₛ F) : F :=
  f.setToSimpleFunc (weightedSMul μ)
#align measure_theory.simple_func.integral MeasureTheory.SimpleFunc.integral

def {_ : MeasurableSpace α} (μ : Measure α) (f : α →ₛ F) :
    f.integral μ = f.setToSimpleFunc (weightedSMul μ) := rfl
#align measure_theory.simple_func.integral_def MeasureTheory.SimpleFunc.integral_def

def posPart (f : α →₁ₛ[μ] ℝ) : α →₁ₛ[μ] ℝ :=
  ⟨Lp.posPart (f : α →₁[μ] ℝ), by
    rcases f with ⟨f, s, hsf⟩
    use s.posPart
    simp only [Subtype.coe_mk, Lp.coe_posPart, ← hsf, AEEqFun.posPart_mk,
      SimpleFunc.coe_map, mk_eq_mk]
    -- Porting note: added
    simp [SimpleFunc.posPart, Function.comp, EventuallyEq.rfl] ⟩
#align measure_theory.L1.simple_func.pos_part MeasureTheory.L1.SimpleFunc.posPart

def negPart (f : α →₁ₛ[μ] ℝ) : α →₁ₛ[μ] ℝ :=
  posPart (-f)
#align measure_theory.L1.simple_func.neg_part MeasureTheory.L1.SimpleFunc.negPart

def integral (f : α →₁ₛ[μ] E) : E :=
  (toSimpleFunc f).integral μ
#align measure_theory.L1.simple_func.integral MeasureTheory.L1.SimpleFunc.integral

def integralCLM' : (α →₁ₛ[μ] E) →L[𝕜] E :=
  LinearMap.mkContinuous ⟨⟨integral, integral_add⟩, integral_smul⟩ 1 fun f =>
    le_trans (norm_integral_le_norm _) <| by rw [one_mul]
#align measure_theory.L1.simple_func.integral_clm' MeasureTheory.L1.SimpleFunc.integralCLM'

def integralCLM : (α →₁ₛ[μ] E) →L[ℝ] E :=
  integralCLM' α E ℝ μ
#align measure_theory.L1.simple_func.integral_clm MeasureTheory.L1.SimpleFunc.integralCLM

def integralCLM' : (α →₁[μ] E) →L[𝕜] E :=
  (integralCLM' α E 𝕜 μ).extend (coeToLp α E 𝕜) (simpleFunc.denseRange one_ne_top)
    simpleFunc.uniformInducing
#align measure_theory.L1.integral_clm' MeasureTheory.L1.integralCLM'

def integralCLM : (α →₁[μ] E) →L[ℝ] E :=
  integralCLM' ℝ
#align measure_theory.L1.integral_clm MeasureTheory.L1.integralCLM

def integral (f : α →₁[μ] E) : E :=
  integralCLM (E := E) f
#align measure_theory.L1.integral MeasureTheory.L1.integral

def integral {_ : MeasurableSpace α} (μ : Measure α) (f : α → G) : G :=
  if _ : CompleteSpace G then
    if hf : Integrable f μ then L1.integral (hf.toL1 f) else 0
  else 0
#align measure_theory.integral MeasureTheory.integral

def {f : α → G} (h : ¬Integrable f μ) : ∫ a, f a ∂μ = 0 := by
  by_cases hG : CompleteSpace G
  · simp [integral, hG, h]
  · simp [integral, hG]
#align measure_theory.integral_undef MeasureTheory.integral_undef

def h

theorem integral_non_aestronglyMeasurable {f : α → G} (h : ¬AEStronglyMeasurable f μ) :
    ∫ a, f a ∂μ = 0 :=
  integral_undef <| not_and_of_not_left _ h
#align measure_theory.integral_non_ae_strongly_measurable MeasureTheory.integral_non_aestronglyMeasurable

def hf, norm_zero]; exact toReal_nonneg
  · simp [integral, hG]
#align measure_theory.norm_integral_le_lintegral_norm MeasureTheory.norm_integral_le_lintegral_norm

def hfi]
    simp_rw [Integrable, hfm, hasFiniteIntegral_iff_norm, lt_top_iff_ne_top, Ne, true_and_iff,
      Classical.not_not] at hfi
    have : ∫⁻ a : α, ENNReal.ofReal (f a) ∂μ = ∫⁻ a, ENNReal.ofReal ‖f a‖ ∂μ := by
      refine' lintegral_congr_ae (hf.mono fun a h => _)
      dsimp only
      rw [Real.norm_eq_abs, abs_of_nonneg h]
    rw [this, hfi]; rfl
#align measure_theory.integral_eq_lintegral_of_nonneg_ae MeasureTheory.integral_eq_lintegral_of_nonneg_ae

def hf]; exact b.2
#align measure_theory.integral_coe_le_of_lintegral_coe_le MeasureTheory.integral_coe_le_of_lintegral_coe_le

def hfi, integral_undef]
    exact fun hfφ => hfi ((integrable_map_measure hfm.aestronglyMeasurable hφ.aemeasurable).2 hfφ)
  borelize G
  have : SeparableSpace (range f ∪ {0} : Set G) := hfm.separableSpace_range_union_singleton
  refine' tendsto_nhds_unique
    (tendsto_integral_approxOn_of_measurable_of_range_subset hfm.measurable hfi _ Subset.rfl) _
  convert tendsto_integral_approxOn_of_measurable_of_range_subset (hfm.measurable.comp hφ)
    ((integrable_map_measure hfm.aestronglyMeasurable hφ.aemeasurable).1 hfi) (range f ∪ {0})
    (by simp [insert_subset_insert, Set.range_comp_subset_range]) using 1
  ext1 i
  simp only [SimpleFunc.approxOn_comp, SimpleFunc.integral_eq, Measure.map_apply, hφ,
    SimpleFunc.measurableSet_preimage, ← preimage_comp, SimpleFunc.coe_comp]
  refine' (Finset.sum_subset (SimpleFunc.range_comp_subset_range _ hφ) fun y _ hy => _).symm
  rw [SimpleFunc.mem_range, ← Set.preimage_singleton_eq_empty, SimpleFunc.coe_comp] at hy
  rw [hy]
  simp
#align measure_theory.integral_map_of_strongly_measurable MeasureTheory.integral_map_of_stronglyMeasurable

def SimpleFunc.toLargerSpace (hm : m ≤ m0) (f : @SimpleFunc β m γ) : SimpleFunc β γ :=
  ⟨@SimpleFunc.toFun β m γ f, fun x => hm _ (@SimpleFunc.measurableSet_fiber β γ m f x),
    @SimpleFunc.finite_range β γ m f⟩
#align measure_theory.simple_func.to_larger_space MeasureTheory.SimpleFunc.toLargerSpace

def hf_int, integral_undef hf_int_m]
  haveI : SeparableSpace (range f ∪ {0} : Set G) := hf.separableSpace_range_union_singleton
  let f_seq := @SimpleFunc.approxOn G β _ _ _ m _ hf.measurable (range f ∪ {0}) 0 (by simp) _
  have hf_seq_meas : ∀ n, StronglyMeasurable[m] (f_seq n) := fun n =>
    @SimpleFunc.stronglyMeasurable β G m _ (f_seq n)
  have hf_seq_int : ∀ n, Integrable (f_seq n) μ :=
    SimpleFunc.integrable_approxOn_range (hf.mono hm).measurable hf_int
  have hf_seq_int_m : ∀ n, Integrable (f_seq n) (μ.trim hm) := fun n =>
    (hf_seq_int n).trim hm (hf_seq_meas n)
  have hf_seq_eq : ∀ n, ∫ x, f_seq n x ∂μ = ∫ x, f_seq n x ∂μ.trim hm := fun n =>
    integral_trim_simpleFunc hm (f_seq n) (hf_seq_int n)
  have h_lim_1 : atTop.Tendsto (fun n => ∫ x, f_seq n x ∂μ) (𝓝 (∫ x, f x ∂μ)) := by
    refine' tendsto_integral_of_L1 f hf_int (eventually_of_forall hf_seq_int) _
    exact SimpleFunc.tendsto_approxOn_range_L1_nnnorm (hf.mono hm).measurable hf_int
  have h_lim_2 : atTop.Tendsto (fun n => ∫ x, f_seq n x ∂μ) (𝓝 (∫ x, f x ∂μ.trim hm)) := by
    simp_rw [hf_seq_eq]
    refine' @tendsto_integral_of_L1 β G _ _ m (μ.trim hm) _ f (hf_int.trim hm hf) _ _
      (eventually_of_forall hf_seq_int_m) _
    exact @SimpleFunc.tendsto_approxOn_range_L1_nnnorm β G m _ _ _ f _ _ hf.measurable
      (hf_int.trim hm hf)
  exact tendsto_nhds_unique h_lim_1 h_lim_2
#align measure_theory.integral_trim MeasureTheory.integral_trim

def evalIntegral : PositivityExt where eval {u α} zα pα e := do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@MeasureTheory.integral $i ℝ _ $inst2 _ _ $f) =>
    let i : Q($i) ← mkFreshExprMVarQ q($i) .syntheticOpaque
    have body : Q(ℝ) := .betaRev f #[i]