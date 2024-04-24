def NullMeasurableSpace (α : Type*) [MeasurableSpace α]
    (_μ : Measure α := by volume_tac) : Type _ :=
  α
#align measure_theory.null_measurable_space MeasureTheory.NullMeasurableSpace

def NullMeasurableSet [MeasurableSpace α] (s : Set α)
    (μ : Measure α := by volume_tac) : Prop :=
  @MeasurableSet (NullMeasurableSpace α μ) _ s
#align measure_theory.null_measurable_set MeasureTheory.NullMeasurableSet

def NullMeasurable (f : α → β) (μ : Measure α := by volume_tac) : Prop :=
  ∀ ⦃s : Set β⦄, MeasurableSet s → NullMeasurableSet (f ⁻¹' s) μ
#align measure_theory.null_measurable MeasureTheory.NullMeasurable

def completion {_ : MeasurableSpace α} (μ : Measure α) :
    @MeasureTheory.Measure (NullMeasurableSpace α μ) _ where
  toOuterMeasure := μ.toOuterMeasure
  m_iUnion s hs hd := measure_iUnion₀ (hd.mono fun i j h => h.aedisjoint) hs
  trimmed := by
    refine' le_antisymm (fun s => _)
      (@OuterMeasure.le_trim (NullMeasurableSpace α μ) _ _)
    rw [@OuterMeasure.trim_eq_iInf (NullMeasurableSpace α μ) _];
    have : ∀ s, μ.toOuterMeasure s = μ s := by simp only [forall_const]
    rw [this, measure_eq_iInf]
    apply iInf₂_mono
    exact fun t _ht => iInf_mono' fun h => ⟨MeasurableSet.nullMeasurableSet h, le_rfl⟩
#align measure_theory.measure.completion MeasureTheory.Measure.completion