def Measure.trim {m m0 : MeasurableSpace α} (μ : @Measure α m0) (hm : m ≤ m0) : @Measure α m :=
  @OuterMeasure.toMeasure α m μ.toOuterMeasure (hm.trans (le_toOuterMeasure_caratheodory μ))
#align measure_theory.measure.trim MeasureTheory.Measure.trim

structure `m0` as being also a measure on
any `m ≤ m0`. Since measures in mathlib have to be trimmed to the measurable space, `μ` itself
cannot be a measure on `m`, hence the definition of `μ.trim hm`.

This notion is related to `OuterMeasure.trim`, see the lemma
`toOuterMeasure_trim_eq_trim_toOuterMeasure`. -/
@[pp_dot]
noncomputable
def Measure.trim {m m0 : MeasurableSpace α} (μ : @Measure α m0) (hm : m ≤ m0) : @Measure α m :=
  @OuterMeasure.toMeasure α m μ.toOuterMeasure (hm.trans (le_toOuterMeasure_caratheodory μ))
#align measure_theory.measure.trim MeasureTheory.Measure.trim