def StronglyMeasurable [MeasurableSpace α] (f : α → β) : Prop :=
  ∃ fs : ℕ → α →ₛ β, ∀ x, Tendsto (fun n => fs n x) atTop (𝓝 (f x))
#align measure_theory.strongly_measurable MeasureTheory.StronglyMeasurable

def FinStronglyMeasurable [Zero β]
    {_ : MeasurableSpace α} (f : α → β) (μ : Measure α := by volume_tac) : Prop :=
  ∃ fs : ℕ → α →ₛ β, (∀ n, μ (support (fs n)) < ∞) ∧ ∀ x, Tendsto (fun n => fs n x) atTop (𝓝 (f x))
#align measure_theory.fin_strongly_measurable MeasureTheory.FinStronglyMeasurable

def AEStronglyMeasurable
    {_ : MeasurableSpace α} (f : α → β) (μ : Measure α := by volume_tac) : Prop :=
  ∃ g, StronglyMeasurable g ∧ f =ᵐ[μ] g
#align measure_theory.ae_strongly_measurable MeasureTheory.AEStronglyMeasurable

def AEFinStronglyMeasurable
    [Zero β] {_ : MeasurableSpace α} (f : α → β) (μ : Measure α := by volume_tac) : Prop :=
  ∃ g, FinStronglyMeasurable g μ ∧ f =ᵐ[μ] g
#align measure_theory.ae_fin_strongly_measurable MeasureTheory.AEFinStronglyMeasurable

def approx {_ : MeasurableSpace α} (hf : StronglyMeasurable f) :
    ℕ → α →ₛ β :=
  hf.choose
#align measure_theory.strongly_measurable.approx MeasureTheory.StronglyMeasurable.approx

def approxBounded {_ : MeasurableSpace α} [Norm β] [SMul ℝ β]
    (hf : StronglyMeasurable f) (c : ℝ) : ℕ → SimpleFunc α β := fun n =>
  (hf.approx n).map fun x => min 1 (c / ‖x‖) • x
#align measure_theory.strongly_measurable.approx_bounded MeasureTheory.StronglyMeasurable.approxBounded

def approx : ℕ → α →ₛ β :=
  hf.choose
#align measure_theory.fin_strongly_measurable.approx MeasureTheory.FinStronglyMeasurable.approx

def mk (f : α → β) (hf : AEStronglyMeasurable f μ) : α → β :=
  hf.choose
#align measure_theory.ae_strongly_measurable.mk MeasureTheory.AEStronglyMeasurable.mk

def mk (f : α → β) (hf : AEFinStronglyMeasurable f μ) : α → β :=
  hf.choose
#align measure_theory.ae_fin_strongly_measurable.mk MeasureTheory.AEFinStronglyMeasurable.mk

def sigmaFiniteSet (hf : AEFinStronglyMeasurable f μ) : Set α :=
  hf.exists_set_sigmaFinite.choose
#align measure_theory.ae_fin_strongly_measurable.sigma_finite_set MeasureTheory.AEFinStronglyMeasurable.sigmaFiniteSet