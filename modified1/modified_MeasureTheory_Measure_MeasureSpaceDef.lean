def from "leanprover-community/mathlib"@"c14c8fcde993801fca8946b0d80131a1a81d1520"

/-!
# Measure spaces

def ofMeasurable (m : ∀ s : Set α, MeasurableSet s → ℝ≥0∞) (m0 : m ∅ MeasurableSet.empty = 0)
    (mU :
      ∀ ⦃f : ℕ → Set α⦄ (h : ∀ i, MeasurableSet (f i)),
        Pairwise (Disjoint on f) → m (⋃ i, f i) (MeasurableSet.iUnion h) = ∑' i, m (f i) (h i)) :
    Measure α :=
  { inducedOuterMeasure m _ m0 with
    m_iUnion := fun f hf hd =>
      show inducedOuterMeasure m _ m0 (iUnion f) = ∑' i, inducedOuterMeasure m _ m0 (f i) by
        rw [inducedOuterMeasure_eq m0 mU, mU hf hd]
        congr; funext n; rw [inducedOuterMeasure_eq m0 mU]
    trimmed :=
      show (inducedOuterMeasure m _ m0).trim = inducedOuterMeasure m _ m0 by
        unfold OuterMeasure.trim
        congr; funext s hs
        exact inducedOuterMeasure_eq m0 mU hs }
#align measure_theory.measure.of_measurable MeasureTheory.Measure.ofMeasurable

def Measure.ae {α : Type*} {_m : MeasurableSpace α} (μ : Measure α) : Filter α :=
  ofCountableUnion (μ · = 0) (fun _S hSc ↦ (measure_sUnion_null_iff hSc).2) fun _t ht _s hs ↦
    measure_mono_null hs ht
#align measure_theory.measure.ae MeasureTheory.Measure.ae

def toMeasurable (μ : Measure α) (s : Set α) : Set α :=
  if h : ∃ t, t ⊇ s ∧ MeasurableSet t ∧ t =ᵐ[μ] s then h.choose else
    if h' : ∃ t, t ⊇ s ∧ MeasurableSet t ∧
      ∀ u, MeasurableSet u → μ (t ∩ u) = μ (s ∩ u) then h'.choose
    else (exists_measurable_superset μ s).choose
#align measure_theory.to_measurable MeasureTheory.toMeasurable

def AEMeasurable {_m : MeasurableSpace α} (f : α → β) (μ : Measure α := by volume_tac) : Prop :=
  ∃ g : α → β, Measurable g ∧ f =ᵐ[μ] g
#align ae_measurable AEMeasurable

def mk (f : α → β) (h : AEMeasurable f μ) : α → β :=
  Classical.choose h
#align ae_measurable.mk AEMeasurable.mk

structure Measure (α : Type*) [MeasurableSpace α] extends OuterMeasure α where
  m_iUnion ⦃f : ℕ → Set α⦄ :
    (∀ i, MeasurableSet (f i)) →
      Pairwise (Disjoint on f) → measureOf (⋃ i, f i) = ∑' i, measureOf (f i)
  trimmed : toOuterMeasure.trim = toOuterMeasure
#align measure_theory.measure MeasureTheory.Measure