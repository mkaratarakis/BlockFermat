def ofFinite [Finite α] [MeasurableSingletonClass α] (f : α → β) : α →ₛ β where
  toFun := f
  measurableSet_fiber' x := (toFinite (f ⁻¹' {x})).measurableSet
  finite_range' := Set.finite_range f

@[deprecated] -- Since 2024/02/05
alias ofFintype := ofFinite

/-- Simple function defined on the empty type. -/
def ofIsEmpty [IsEmpty α] : α →ₛ β := ofFinite isEmptyElim
#align measure_theory.simple_func.of_is_empty MeasureTheory.SimpleFunc.ofIsEmpty

def range (f : α →ₛ β) : Finset β :=
  f.finite_range.toFinset
#align measure_theory.simple_func.range MeasureTheory.SimpleFunc.range

def const (α) {β} [MeasurableSpace α] (b : β) : α →ₛ β :=
  ⟨fun _ => b, fun _ => MeasurableSet.const _, finite_range_const⟩
#align measure_theory.simple_func.const MeasureTheory.SimpleFunc.const

def piecewise (s : Set α) (hs : MeasurableSet s) (f g : α →ₛ β) : α →ₛ β :=
  ⟨s.piecewise f g, fun _ =>
    letI : MeasurableSpace β := ⊤
    f.measurable.piecewise hs g.measurable trivial,
    (f.finite_range.union g.finite_range).subset range_ite_subset⟩
#align measure_theory.simple_func.piecewise MeasureTheory.SimpleFunc.piecewise

def bind (f : α →ₛ β) (g : β → α →ₛ γ) : α →ₛ γ :=
  ⟨fun a => g (f a) a, fun c =>
    f.measurableSet_cut (fun a b => g b a = c) fun b => (g b).measurableSet_preimage {c},
    (f.finite_range.biUnion fun b _ => (g b).finite_range).subset <| by
      rintro _ ⟨a, rfl⟩; simp; exact ⟨a, a, rfl⟩⟩
#align measure_theory.simple_func.bind MeasureTheory.SimpleFunc.bind

def map (g : β → γ) (f : α →ₛ β) : α →ₛ γ :=
  bind f (const α ∘ g)
#align measure_theory.simple_func.map MeasureTheory.SimpleFunc.map

def comp [MeasurableSpace β] (f : β →ₛ γ) (g : α → β) (hgm : Measurable g) : α →ₛ γ where
  toFun := f ∘ g
  finite_range' := f.finite_range.subset <| Set.range_comp_subset_range _ _
  measurableSet_fiber' z := hgm (f.measurableSet_fiber z)
#align measure_theory.simple_func.comp MeasureTheory.SimpleFunc.comp

def extend [MeasurableSpace β] (f₁ : α →ₛ γ) (g : α → β) (hg : MeasurableEmbedding g)
    (f₂ : β →ₛ γ) : β →ₛ γ where
  toFun := Function.extend g f₁ f₂
  finite_range' :=
    (f₁.finite_range.union <| f₂.finite_range.subset (image_subset_range _ _)).subset
      (range_extend_subset _ _ _)
  measurableSet_fiber' := by
    letI : MeasurableSpace γ := ⊤; haveI : MeasurableSingletonClass γ := ⟨fun _ => trivial⟩
    exact fun x => hg.measurable_extend f₁.measurable f₂.measurable (measurableSet_singleton _)
#align measure_theory.simple_func.extend MeasureTheory.SimpleFunc.extend

def seq (f : α →ₛ β → γ) (g : α →ₛ β) : α →ₛ γ :=
  f.bind fun f => g.map f
#align measure_theory.simple_func.seq MeasureTheory.SimpleFunc.seq

def pair (f : α →ₛ β) (g : α →ₛ γ) : α →ₛ β × γ :=
  (f.map Prod.mk).seq g
#align measure_theory.simple_func.pair MeasureTheory.SimpleFunc.pair

def restrict (f : α →ₛ β) (s : Set α) : α →ₛ β :=
  if hs : MeasurableSet s then piecewise s hs f 0 else 0
#align measure_theory.simple_func.restrict MeasureTheory.SimpleFunc.restrict

def approx (i : ℕ → β) (f : α → β) (n : ℕ) : α →ₛ β :=
  (Finset.range n).sup fun k => restrict (const α (i k)) { a : α | i k ≤ f a }
#align measure_theory.simple_func.approx MeasureTheory.SimpleFunc.approx

def ennrealRatEmbed (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((Encodable.decode (α := ℚ) n).getD (0 : ℚ))
#align measure_theory.simple_func.ennreal_rat_embed MeasureTheory.SimpleFunc.ennrealRatEmbed

def eapprox : (α → ℝ≥0∞) → ℕ → α →ₛ ℝ≥0∞ :=
  approx ennrealRatEmbed
#align measure_theory.simple_func.eapprox MeasureTheory.SimpleFunc.eapprox

def eapproxDiff (f : α → ℝ≥0∞) : ℕ → α →ₛ ℝ≥0
  | 0 => (eapprox f 0).map ENNReal.toNNReal
  | n + 1 => (eapprox f (n + 1) - eapprox f n).map ENNReal.toNNReal
#align measure_theory.simple_func.eapprox_diff MeasureTheory.SimpleFunc.eapproxDiff

def lintegral {_m : MeasurableSpace α} (f : α →ₛ ℝ≥0∞) (μ : Measure α) : ℝ≥0∞ :=
  ∑ x in f.range, x * μ (f ⁻¹' {x})
#align measure_theory.simple_func.lintegral MeasureTheory.SimpleFunc.lintegral

def lintegralₗ {m : MeasurableSpace α} : (α →ₛ ℝ≥0∞) →ₗ[ℝ≥0∞] Measure α →ₗ[ℝ≥0∞] ℝ≥0∞ where
  toFun f :=
    { toFun := lintegral f
      map_add' := by simp [lintegral, mul_add, Finset.sum_add_distrib]
      map_smul' := fun c μ => by
        simp [lintegral, mul_left_comm _ c, Finset.mul_sum, Measure.smul_apply c] }
  map_add' f g := LinearMap.ext fun μ => add_lintegral f g
  map_smul' c f := LinearMap.ext fun μ => const_mul_lintegral f c
#align measure_theory.simple_func.lintegralₗ MeasureTheory.SimpleFunc.lintegralₗ

def FinMeasSupp {_m : MeasurableSpace α} (f : α →ₛ β) (μ : Measure α) : Prop :=
  f =ᶠ[μ.cofinite] 0
#align measure_theory.simple_func.fin_meas_supp MeasureTheory.SimpleFunc.FinMeasSupp

structure bundles
a function with these properties. -/
structure SimpleFunc.{u, v} (α : Type u) [MeasurableSpace α] (β : Type v) where
  toFun : α → β
  measurableSet_fiber' : ∀ x, MeasurableSet (toFun ⁻¹' {x})
  finite_range' : (Set.range toFun).Finite
#align measure_theory.simple_func MeasureTheory.SimpleFunc