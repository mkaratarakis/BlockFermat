def Measure.withDensity {m : MeasurableSpace α} (μ : Measure α) (f : α → ℝ≥0∞) : Measure α :=
  Measure.ofMeasurable (fun s _ => ∫⁻ a in s, f a ∂μ) (by simp) fun s hs hd =>
    lintegral_iUnion hs hd _
#align measure_theory.measure.with_density MeasureTheory.Measure.withDensity