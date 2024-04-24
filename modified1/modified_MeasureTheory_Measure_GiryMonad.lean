def join (m : Measure (Measure α)) : Measure α :=
  Measure.ofMeasurable (fun s _ => ∫⁻ μ, μ s ∂m)
    (by simp only [measure_empty, lintegral_const, zero_mul])
    (by
      intro f hf h
      simp_rw [measure_iUnion h hf]
      apply lintegral_tsum
      intro i; exact (measurable_coe (hf i)).aemeasurable)
#align measure_theory.measure.join MeasureTheory.Measure.join

def bind (m : Measure α) (f : α → Measure β) : Measure β :=
  join (map f m)
#align measure_theory.measure.bind MeasureTheory.Measure.bind

structure on `Measure`: Measures are measurable w.r.t. all projections -/
instance instMeasurableSpace : MeasurableSpace (Measure α) :=
  ⨆ (s : Set α) (_ : MeasurableSet s), (borel ℝ≥0∞).comap fun μ => μ s
#align measure_theory.measure.measurable_space MeasureTheory.Measure.instMeasurableSpace