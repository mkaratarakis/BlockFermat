def inv [Inv G] (μ : Measure G) : Measure G :=
  Measure.map inv μ
#align measure_theory.measure.inv MeasureTheory.Measure.inv

def (μ : Measure G) : μ.inv = Measure.map inv μ := rfl

@[to_additive (attr := simp)]
theorem inv_eq_self (μ : Measure G) [IsInvInvariant μ] : μ.inv = μ :=
  IsInvInvariant.inv_eq_self
#align measure_theory.measure.inv_eq_self MeasureTheory.Measure.inv_eq_self