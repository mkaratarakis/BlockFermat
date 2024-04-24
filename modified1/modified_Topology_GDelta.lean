def IsGδ (s : Set X) : Prop :=
  ∃ T : Set (Set X), (∀ t ∈ T, IsOpen t) ∧ T.Countable ∧ s = ⋂₀ T
#align is_Gδ IsGδ

def residual (X : Type*) [TopologicalSpace X] : Filter X :=
  Filter.countableGenerate { t | IsOpen t ∧ Dense t }
#align residual residual