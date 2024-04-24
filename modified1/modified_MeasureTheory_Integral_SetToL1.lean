def FinMeasAdditive {β} [AddMonoid β] {_ : MeasurableSpace α} (μ : Measure α) (T : Set α → β) :
    Prop :=
  ∀ s t, MeasurableSet s → MeasurableSet t → μ s ≠ ∞ → μ t ≠ ∞ → s ∩ t = ∅ → T (s ∪ t) = T s + T t
#align measure_theory.fin_meas_additive MeasureTheory.FinMeasAdditive

def DominatedFinMeasAdditive {β} [SeminormedAddCommGroup β] {_ : MeasurableSpace α} (μ : Measure α)
    (T : Set α → β) (C : ℝ) : Prop :=
  FinMeasAdditive μ T ∧ ∀ s, MeasurableSet s → μ s < ∞ → ‖T s‖ ≤ C * (μ s).toReal
#align measure_theory.dominated_fin_meas_additive MeasureTheory.DominatedFinMeasAdditive

def setToSimpleFunc {_ : MeasurableSpace α} (T : Set α → F →L[ℝ] F') (f : α →ₛ F) : F' :=
  ∑ x in f.range, T (f ⁻¹' {x}) x
#align measure_theory.simple_func.set_to_simple_func MeasureTheory.SimpleFunc.setToSimpleFunc

def setToL1S (T : Set α → E →L[ℝ] F) (f : α →₁ₛ[μ] E) : F :=
  (toSimpleFunc f).setToSimpleFunc T
#align measure_theory.L1.simple_func.set_to_L1s MeasureTheory.L1.SimpleFunc.setToL1S

def setToL1SCLM' {T : Set α → E →L[ℝ] F} {C : ℝ} (hT : DominatedFinMeasAdditive μ T C)
    (h_smul : ∀ c : 𝕜, ∀ s x, T s (c • x) = c • T s x) : (α →₁ₛ[μ] E) →L[𝕜] F :=
  LinearMap.mkContinuous
    ⟨⟨setToL1S T, setToL1S_add T (fun _ => hT.eq_zero_of_measure_zero) hT.1⟩,
      setToL1S_smul T (fun _ => hT.eq_zero_of_measure_zero) hT.1 h_smul⟩
    C fun f => norm_setToL1S_le T hT.2 f
#align measure_theory.L1.simple_func.set_to_L1s_clm' MeasureTheory.L1.SimpleFunc.setToL1SCLM'

def setToL1SCLM {T : Set α → E →L[ℝ] F} {C : ℝ} (hT : DominatedFinMeasAdditive μ T C) :
    (α →₁ₛ[μ] E) →L[ℝ] F :=
  LinearMap.mkContinuous
    ⟨⟨setToL1S T, setToL1S_add T (fun _ => hT.eq_zero_of_measure_zero) hT.1⟩,
      setToL1S_smul_real T (fun _ => hT.eq_zero_of_measure_zero) hT.1⟩
    C fun f => norm_setToL1S_le T hT.2 f
#align measure_theory.L1.simple_func.set_to_L1s_clm MeasureTheory.L1.SimpleFunc.setToL1SCLM

def setToL1' (hT : DominatedFinMeasAdditive μ T C)
    (h_smul : ∀ c : 𝕜, ∀ s x, T s (c • x) = c • T s x) : (α →₁[μ] E) →L[𝕜] F :=
  (setToL1SCLM' α E 𝕜 μ hT h_smul).extend (coeToLp α E 𝕜) (simpleFunc.denseRange one_ne_top)
    simpleFunc.uniformInducing
#align measure_theory.L1.set_to_L1' MeasureTheory.L1.setToL1'

def setToL1 (hT : DominatedFinMeasAdditive μ T C) : (α →₁[μ] E) →L[ℝ] F :=
  (setToL1SCLM α E μ hT).extend (coeToLp α E ℝ) (simpleFunc.denseRange one_ne_top)
    simpleFunc.uniformInducing
#align measure_theory.L1.set_to_L1 MeasureTheory.L1.setToL1

def setToFun (hT : DominatedFinMeasAdditive μ T C) (f : α → E) : F :=
  if hf : Integrable f μ then L1.setToL1 hT (hf.toL1 f) else 0
#align measure_theory.set_to_fun MeasureTheory.setToFun

def (hT : DominatedFinMeasAdditive μ T C) (hf : ¬Integrable f μ) :
    setToFun μ T hT f = 0 :=
  dif_neg hf
#align measure_theory.set_to_fun_undef MeasureTheory.setToFun_undef

def hT (not_and_of_not_left _ hf)
#align measure_theory.set_to_fun_non_ae_strongly_measurable MeasureTheory.setToFun_non_aEStronglyMeasurable

def _ hf]
#align measure_theory.set_to_fun_congr_left MeasureTheory.setToFun_congr_left

def _ hf]
#align measure_theory.set_to_fun_congr_left' MeasureTheory.setToFun_congr_left'

def _ hf, add_zero]
#align measure_theory.set_to_fun_add_left MeasureTheory.setToFun_add_left

def _ hf, add_zero]
#align measure_theory.set_to_fun_add_left' MeasureTheory.setToFun_add_left'

def _ hf, smul_zero]
#align measure_theory.set_to_fun_smul_left MeasureTheory.setToFun_smul_left

def _ hf, smul_zero]
#align measure_theory.set_to_fun_smul_left' MeasureTheory.setToFun_smul_left'

def hT hf
#align measure_theory.set_to_fun_zero_left MeasureTheory.setToFun_zero_left

def hT hf
#align measure_theory.set_to_fun_zero_left' MeasureTheory.setToFun_zero_left'

def hT hf, setToFun_undef hT, neg_zero]
    rwa [← integrable_neg_iff] at hf
#align measure_theory.set_to_fun_neg MeasureTheory.setToFun_neg

def hT hf, setToFun_undef hT hf', smul_zero]
#align measure_theory.set_to_fun_smul MeasureTheory.setToFun_smul

def hT hfi, setToFun_undef hT hgi]
#align measure_theory.set_to_fun_congr_ae MeasureTheory.setToFun_congr_ae

def _ hf]; rfl
#align measure_theory.set_to_fun_mono_left' MeasureTheory.setToFun_mono_left'

def _ hfi]; rfl
#align measure_theory.set_to_fun_nonneg MeasureTheory.setToFun_nonneg

def _ hf, setToFun_undef _ (h_int f hf)]
#align measure_theory.set_to_fun_congr_measure MeasureTheory.setToFun_congr_measure