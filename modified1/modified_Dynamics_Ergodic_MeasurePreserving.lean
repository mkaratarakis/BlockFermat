structure MeasurePreserving (f : α → β)
  (μa : Measure α := by volume_tac) (μb : Measure β := by volume_tac) : Prop where
  protected measurable : Measurable f
  protected map_eq : map f μa = μb
#align measure_theory.measure_preserving MeasureTheory.MeasurePreserving