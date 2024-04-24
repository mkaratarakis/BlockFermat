def id : StieltjesFunction where
  toFun := id
  mono' _ _ := id
  right_continuous' _ := continuousWithinAt_id
#align stieltjes_function.id StieltjesFunction.id

def _root_.Monotone.stieltjesFunction {f : ℝ → ℝ} (hf : Monotone f) :
    StieltjesFunction where
  toFun := rightLim f
  mono' x y hxy := hf.rightLim hxy
  right_continuous' := by
    intro x s hs
    obtain ⟨l, u, hlu, lus⟩ : ∃ l u : ℝ, rightLim f x ∈ Ioo l u ∧ Ioo l u ⊆ s :=
      mem_nhds_iff_exists_Ioo_subset.1 hs
    obtain ⟨y, xy, h'y⟩ : ∃ (y : ℝ), x < y ∧ Ioc x y ⊆ f ⁻¹' Ioo l u :=
      mem_nhdsWithin_Ioi_iff_exists_Ioc_subset.1 (hf.tendsto_rightLim x (Ioo_mem_nhds hlu.1 hlu.2))
    change ∀ᶠ y in 𝓝[≥] x, rightLim f y ∈ s
    filter_upwards [Ico_mem_nhdsWithin_Ici ⟨le_refl x, xy⟩] with z hz
    apply lus
    refine' ⟨hlu.1.trans_le (hf.rightLim hz.1), _⟩
    obtain ⟨a, za, ay⟩ : ∃ a : ℝ, z < a ∧ a < y := exists_between hz.2
    calc
      rightLim f z ≤ f a := hf.rightLim_le za
      _ < u := (h'y ⟨hz.1.trans_lt za, ay.le⟩).2
#align monotone.stieltjes_function Monotone.stieltjesFunction

def length (s : Set ℝ) : ℝ≥0∞ :=
  ⨅ (a) (b) (_ : s ⊆ Ioc a b), ofReal (f b - f a)
#align stieltjes_function.length StieltjesFunction.length

def outer : OuterMeasure ℝ :=
  OuterMeasure.ofFunction f.length f.length_empty
#align stieltjes_function.outer StieltjesFunction.outer

def measure : Measure ℝ :=
  { toOuterMeasure := f.outer
    m_iUnion := fun _s hs =>
      f.outer.iUnion_eq_of_caratheodory fun i => f.borel_le_measurable _ (hs i)
    trimmed := f.outer_trim }
#align stieltjes_function.measure StieltjesFunction.measure

structure containing a function from `ℝ → ℝ`, together with the
assertions that it is monotone and right-continuous. To `f : StieltjesFunction`, one associates
a Borel measure `f.measure`.
* `f.measure_Ioc` asserts that `f.measure (Ioc a b) = ofReal (f b - f a)`
* `f.measure_Ioo` asserts that `f.measure (Ioo a b) = ofReal (leftLim f b - f a)`.
* `f.measure_Icc` and `f.measure_Ico` are analogous.
-/

noncomputable section

open scoped Classical
open Set Filter Function BigOperators ENNReal NNReal Topology MeasureTheory

open ENNReal (ofReal)


/-! ### Basic properties of Stieltjes functions -/

structure StieltjesFunction where
  toFun : ℝ → ℝ
  mono' : Monotone toFun
  right_continuous' : ∀ x, ContinuousWithinAt toFun (Ici x) x
#align stieltjes_function StieltjesFunction