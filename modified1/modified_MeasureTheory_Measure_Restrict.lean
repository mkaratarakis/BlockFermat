def restrictₗ {m0 : MeasurableSpace α} (s : Set α) : Measure α →ₗ[ℝ≥0∞] Measure α :=
  liftLinear (OuterMeasure.restrict s) fun μ s' hs' t => by
    suffices μ (s ∩ t) = μ (s ∩ t ∩ s') + μ ((s ∩ t) \ s') by
      simpa [← Set.inter_assoc, Set.inter_comm _ s, ← inter_diff_assoc]
    exact le_toOuterMeasure_caratheodory _ _ hs' _
#align measure_theory.measure.restrictₗ MeasureTheory.Measure.restrictₗ

def restrict {_m0 : MeasurableSpace α} (μ : Measure α) (s : Set α) : Measure α :=
  restrictₗ s μ
#align measure_theory.measure.restrict MeasureTheory.Measure.restrict

def Subtype.measureSpace : MeasureSpace (Subtype p) where
  volume := Measure.comap Subtype.val volume
#align measure_theory.measure.subtype.measure_space MeasureTheory.Measure.Subtype.measureSpace

def : (volume : Measure u) = volume.comap Subtype.val :=
  rfl
#align measure_theory.measure.subtype.volume_def MeasureTheory.Measure.Subtype.volume_def

def (s : Set α) : (volume : Measure s) = comap ((↑) : s → α) volume :=
  rfl
#align volume_set_coe_def volume_set_coe_def