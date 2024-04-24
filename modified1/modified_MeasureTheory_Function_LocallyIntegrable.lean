def LocallyIntegrableOn (f : X → E) (s : Set X) (μ : Measure X := by volume_tac) : Prop :=
  ∀ x : X, x ∈ s → IntegrableAtFilter f (𝓝[s] x) μ
#align measure_theory.locally_integrable_on MeasureTheory.LocallyIntegrableOn

def LocallyIntegrable (f : X → E) (μ : Measure X := by volume_tac) : Prop :=
  ∀ x : X, IntegrableAtFilter f (𝓝 x) μ
#align measure_theory.locally_integrable MeasureTheory.LocallyIntegrable