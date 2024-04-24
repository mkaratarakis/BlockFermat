def MutuallySingular {_ : MeasurableSpace α} (μ ν : Measure α) : Prop :=
  ∃ s : Set α, MeasurableSet s ∧ μ s = 0 ∧ ν sᶜ = 0
#align measure_theory.measure.mutually_singular MeasureTheory.Measure.MutuallySingular

def nullSet (h : μ ⟂ₘ ν) : Set α := h.choose

lemma measurableSet_nullSet (h : μ ⟂ₘ ν) : MeasurableSet h.nullSet := h.choose_spec.1

@[simp]
lemma measure_nullSet (h : μ ⟂ₘ ν) : μ h.nullSet = 0 := h.choose_spec.2.1

@[simp]
lemma measure_compl_nullSet (h : μ ⟂ₘ ν) : ν h.nullSetᶜ = 0 := h.choose_spec.2.2

-- TODO: this is proved by simp, but is not simplified in other contexts without the @[simp]
-- attribute. Also, the linter does not complain about that attribute.
@[simp]
lemma restrict_nullSet (h : μ ⟂ₘ ν) : μ.restrict h.nullSet = 0 := by simp

-- TODO: this is proved by simp, but is not simplified in other contexts without the @[simp]
-- attribute. Also, the linter does not complain about that attribute.
@[simp]
lemma restrict_compl_nullSet (h : μ ⟂ₘ ν) : ν.restrict h.nullSetᶜ = 0 := by simp

@[simp]
theorem zero_right : μ ⟂ₘ 0 :=
  ⟨∅, MeasurableSet.empty, measure_empty, rfl⟩
#align measure_theory.measure.mutually_singular.zero_right MeasureTheory.Measure.MutuallySingular.zero_right