def StronglyMeasurableAtFilter (f : α → β) (l : Filter α) (μ : Measure α := by volume_tac) :=
  ∃ s ∈ l, AEStronglyMeasurable f (μ.restrict s)
#align strongly_measurable_at_filter StronglyMeasurableAtFilter

def IntegrableOn (f : α → E) (s : Set α) (μ : Measure α := by volume_tac) : Prop :=
  Integrable f (μ.restrict s)
#align measure_theory.integrable_on MeasureTheory.IntegrableOn

def IntegrableAtFilter (f : α → E) (l : Filter α) (μ : Measure α := by volume_tac) :=
  ∃ s ∈ l, IntegrableOn f s μ
#align measure_theory.integrable_at_filter MeasureTheory.IntegrableAtFilter