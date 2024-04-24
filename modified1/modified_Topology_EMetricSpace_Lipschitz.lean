def LipschitzWith [PseudoEMetricSpace α] [PseudoEMetricSpace β] (K : ℝ≥0) (f : α → β) :=
  ∀ x y, edist (f x) (f y) ≤ K * edist x y
#align lipschitz_with LipschitzWith

def LipschitzOnWith [PseudoEMetricSpace α] [PseudoEMetricSpace β] (K : ℝ≥0) (f : α → β)
    (s : Set α) :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → edist (f x) (f y) ≤ K * edist x y
#align lipschitz_on_with LipschitzOnWith

def LocallyLipschitz [PseudoEMetricSpace α] [PseudoEMetricSpace β] (f : α → β) : Prop :=
  ∀ x : α, ∃ K, ∃ t ∈ 𝓝 x, LipschitzOnWith K f t

/-- Every function is Lipschitz on the empty set (with any Lipschitz constant). -/
@[simp]
theorem lipschitzOnWith_empty [PseudoEMetricSpace α] [PseudoEMetricSpace β] (K : ℝ≥0) (f : α → β) :
    LipschitzOnWith K f ∅ := fun _ => False.elim
#align lipschitz_on_with_empty lipschitzOnWith_empty