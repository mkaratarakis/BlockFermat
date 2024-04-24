def index (K V : Set G) : ℕ :=
  sInf <| Finset.card '' { t : Finset G | K ⊆ ⋃ g ∈ t, (fun h => g * h) ⁻¹' V }
#align measure_theory.measure.haar.index MeasureTheory.Measure.haar.index

def prehaar (K₀ U : Set G) (K : Compacts G) : ℝ :=
  (index (K : Set G) U : ℝ) / index K₀ U
#align measure_theory.measure.haar.prehaar MeasureTheory.Measure.haar.prehaar

def haarProduct (K₀ : Set G) : Set (Compacts G → ℝ) :=
  pi univ fun K => Icc 0 <| index (K : Set G) K₀
#align measure_theory.measure.haar.haar_product MeasureTheory.Measure.haar.haarProduct

def clPrehaar (K₀ : Set G) (V : OpenNhdsOf (1 : G)) : Set (Compacts G → ℝ) :=
  closure <| prehaar K₀ '' { U : Set G | U ⊆ V.1 ∧ IsOpen U ∧ (1 : G) ∈ U }
#align measure_theory.measure.haar.cl_prehaar MeasureTheory.Measure.haar.clPrehaar

def chaar (K₀ : PositiveCompacts G) (K : Compacts G) : ℝ :=
  Classical.choose (nonempty_iInter_clPrehaar K₀) K
#align measure_theory.measure.haar.chaar MeasureTheory.Measure.haar.chaar

def haarContent (K₀ : PositiveCompacts G) : Content G where
  toFun K := ⟨chaar K₀ K, chaar_nonneg _ _⟩
  mono' K₁ K₂ h := by simp only [← NNReal.coe_le_coe, NNReal.toReal, chaar_mono, h]
  sup_disjoint' K₁ K₂ h _h₁ h₂ := by simp only [chaar_sup_eq h]; rfl
  sup_le' K₁ K₂ := by
    simp only [← NNReal.coe_le_coe, NNReal.coe_add]
    simp only [NNReal.toReal, chaar_sup_le]
#align measure_theory.measure.haar.haar_content MeasureTheory.Measure.haar.haarContent

def haarMeasure (K₀ : PositiveCompacts G) : Measure G :=
  ((haarContent K₀).measure K₀)⁻¹ • (haarContent K₀).measure
#align measure_theory.measure.haar_measure MeasureTheory.Measure.haarMeasure

def haar [LocallyCompactSpace G] : Measure G :=
  haarMeasure <| Classical.arbitrary _
#align measure_theory.measure.haar MeasureTheory.Measure.haar