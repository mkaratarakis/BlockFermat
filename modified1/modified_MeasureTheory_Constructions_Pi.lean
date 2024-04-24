def piPremeasure (m : ∀ i, OuterMeasure (α i)) (s : Set (∀ i, α i)) : ℝ≥0∞ :=
  ∏ i, m i (eval i '' s)
#align measure_theory.pi_premeasure MeasureTheory.piPremeasure

def pi (m : ∀ i, OuterMeasure (α i)) : OuterMeasure (∀ i, α i) :=
  boundedBy (piPremeasure m)
#align measure_theory.outer_measure.pi MeasureTheory.OuterMeasure.pi

def tprod (l : List δ) (μ : ∀ i, Measure (π i)) : Measure (TProd π l) := by
  induction' l with i l ih
  · exact dirac PUnit.unit
  · have := (μ i).prod (α := π i) ih
    exact this
#align measure_theory.measure.tprod MeasureTheory.Measure.tprod

def pi' : Measure (∀ i, α i) :=
  Measure.map (TProd.elim' mem_sortedUniv) (Measure.tprod (sortedUniv ι) μ)
#align measure_theory.measure.pi' MeasureTheory.Measure.pi'

def pi : Measure (∀ i, α i) :=
  toMeasure (OuterMeasure.pi fun i => (μ i).toOuterMeasure) (pi_caratheodory μ)
#align measure_theory.measure.pi MeasureTheory.Measure.pi

def FiniteSpanningSetsIn.pi {C : ∀ i, Set (Set (α i))}
    (hμ : ∀ i, (μ i).FiniteSpanningSetsIn (C i)) :
    (Measure.pi μ).FiniteSpanningSetsIn (pi univ '' pi univ C) := by
  haveI := fun i => (hμ i).sigmaFinite
  haveI := Fintype.toEncodable ι
  refine' ⟨fun n => Set.pi univ fun i => (hμ i).set ((@decode (ι → ℕ) _ n).iget i),
    fun n => _, fun n => _, _⟩ <;>
  -- TODO (kmill) If this let comes before the refine, while the noncomputability checker
  -- correctly sees this definition is computable, the Lean VM fails to see the binding is
  -- computationally irrelevant. The `noncomputable section` doesn't help because all it does
  -- is insert `noncomputable` for you when necessary.
  let e : ℕ → ι → ℕ := fun n => (@decode (ι → ℕ) _ n).iget
  · refine' mem_image_of_mem _ fun i _ => (hμ i).set_mem _
  · calc
      Measure.pi μ (Set.pi univ fun i => (hμ i).set (e n i)) ≤
          Measure.pi μ (Set.pi univ fun i => toMeasurable (μ i) ((hμ i).set (e n i))) :=
        measure_mono (pi_mono fun i _ => subset_toMeasurable _ _)
      _ = ∏ i, μ i (toMeasurable (μ i) ((hμ i).set (e n i))) :=
        (pi_pi_aux μ _ fun i => measurableSet_toMeasurable _ _)
      _ = ∏ i, μ i ((hμ i).set (e n i)) := by simp only [measure_toMeasurable]
      _ < ∞ := ENNReal.prod_lt_top fun i _ => ((hμ i).finite _).ne
  · simp_rw [(surjective_decode_iget (ι → ℕ)).iUnion_comp fun x =>
        Set.pi univ fun i => (hμ i).set (x i),
      iUnion_univ_pi fun i => (hμ i).set, (hμ _).spanning, Set.pi_univ]
#align measure_theory.measure.finite_spanning_sets_in.pi MeasureTheory.Measure.FiniteSpanningSetsIn.pi