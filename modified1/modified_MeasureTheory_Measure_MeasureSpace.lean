def OuterMeasure.toMeasure (m : OuterMeasure α) (h : ms ≤ m.caratheodory) : Measure α :=
  Measure.ofMeasurable (fun s _ => m s) m.empty fun _f hf hd =>
    m.iUnion_eq_of_caratheodory (fun i => h _ (hf i)) hd
#align measure_theory.outer_measure.to_measure MeasureTheory.OuterMeasure.toMeasure

def coeAddHom {_ : MeasurableSpace α} : Measure α →+ Set α → ℝ≥0∞ where
  toFun := (⇑)
  map_zero' := coe_zero
  map_add' := coe_add
#align measure_theory.measure.coe_add_hom MeasureTheory.Measure.coeAddHom

def liftLinear {m0 : MeasurableSpace α} (f : OuterMeasure α →ₗ[ℝ≥0∞] OuterMeasure β)
    (hf : ∀ μ : Measure α, ‹_› ≤ (f μ.toOuterMeasure).caratheodory) : Measure α →ₗ[ℝ≥0∞] Measure β
    where
  toFun μ := (f μ.toOuterMeasure).toMeasure (hf μ)
  map_add' μ₁ μ₂ := ext fun s hs => by
    simp only [map_add, coe_add, Pi.add_apply, toMeasure_apply, add_toOuterMeasure,
      OuterMeasure.coe_add, hs]
  map_smul' c μ := ext fun s hs => by
    simp only [LinearMap.map_smulₛₗ, coe_smul, Pi.smul_apply,
      toMeasure_apply, smul_toOuterMeasure (R := ℝ≥0∞), OuterMeasure.coe_smul (R := ℝ≥0∞),
      smul_apply, hs]
#align measure_theory.measure.lift_linear MeasureTheory.Measure.liftLinear

def mapₗ [MeasurableSpace α] (f : α → β) : Measure α →ₗ[ℝ≥0∞] Measure β :=
  if hf : Measurable f then
    liftLinear (OuterMeasure.map f) fun μ _s hs t =>
      le_toOuterMeasure_caratheodory μ _ (hf hs) (f ⁻¹' t)
  else 0
#align measure_theory.measure.mapₗ MeasureTheory.Measure.mapₗ

def map [MeasurableSpace α] (f : α → β) (μ : Measure α) : Measure β :=
  if hf : AEMeasurable f μ then mapₗ (hf.mk f) μ else 0
#align measure_theory.measure.map MeasureTheory.Measure.map

def comapₗ [MeasurableSpace α] (f : α → β) : Measure β →ₗ[ℝ≥0∞] Measure α :=
  if hf : Injective f ∧ ∀ s, MeasurableSet s → MeasurableSet (f '' s) then
    liftLinear (OuterMeasure.comap f) fun μ s hs t => by
      simp only [OuterMeasure.comap_apply, image_inter hf.1, image_diff hf.1]
      apply le_toOuterMeasure_caratheodory
      exact hf.2 s hs
  else 0
#align measure_theory.measure.comapₗ MeasureTheory.Measure.comapₗ

def comap [MeasurableSpace α] (f : α → β) (μ : Measure β) : Measure α :=
  if hf : Injective f ∧ ∀ s, MeasurableSet s → NullMeasurableSet (f '' s) μ then
    (OuterMeasure.comap f μ.toOuterMeasure).toMeasure fun s hs t => by
      simp only [OuterMeasure.comap_apply, image_inter hf.1, image_diff hf.1]
      exact (measure_inter_add_diff₀ _ (hf.2 s hs)).symm
  else 0
#align measure_theory.measure.comap MeasureTheory.Measure.comap

def sum (f : ι → Measure α) : Measure α :=
  (OuterMeasure.sum fun i => (f i).toOuterMeasure).toMeasure <|
    le_trans (le_iInf fun _ => le_toOuterMeasure_caratheodory _)
      (OuterMeasure.le_sum_caratheodory _)
#align measure_theory.measure.sum MeasureTheory.Measure.sum

def AbsolutelyContinuous {_m0 : MeasurableSpace α} (μ ν : Measure α) : Prop :=
  ∀ ⦃s : Set α⦄, ν s = 0 → μ s = 0
#align measure_theory.measure.absolutely_continuous MeasureTheory.Measure.AbsolutelyContinuous

def cofinite {m0 : MeasurableSpace α} (μ : Measure α) : Filter α :=
  comk (μ · < ∞) (by simp) (fun t ht s hs ↦ (measure_mono hs).trans_lt ht) fun s hs t ht ↦
    (measure_union_le s t).trans_lt <| ENNReal.add_lt_top.2 ⟨hs, ht⟩
#align measure_theory.measure.cofinite MeasureTheory.Measure.cofinite

structure QuasiMeasurePreserving {m0 : MeasurableSpace α} (f : α → β)
  (μa : Measure α := by volume_tac)
  (μb : Measure β := by volume_tac) : Prop where
  protected measurable : Measurable f
  protected absolutelyContinuous : μa.map f ≪ μb
#align measure_theory.measure.quasi_measure_preserving MeasureTheory.Measure.QuasiMeasurePreserving