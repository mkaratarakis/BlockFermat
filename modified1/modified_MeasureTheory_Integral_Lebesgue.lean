def lintegral {_ : MeasurableSpace α} (μ : Measure α) (f : α → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ (g : α →ₛ ℝ≥0∞) (_ : ⇑g ≤ f), g.lintegral μ
#align measure_theory.lintegral MeasureTheory.lintegral