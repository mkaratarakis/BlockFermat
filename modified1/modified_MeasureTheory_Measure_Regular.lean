def InnerRegularWRT {α} {_ : MeasurableSpace α} (μ : Measure α) (p q : Set α → Prop) :=
  ∀ ⦃U⦄, q U → ∀ r < μ U, ∃ K, K ⊆ U ∧ p K ∧ r < μ K
#align measure_theory.measure.inner_regular MeasureTheory.Measure.InnerRegularWRT