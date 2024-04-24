def prod (μ : Measure α) (ν : Measure β) : Measure (α × β) :=
  bind μ fun x : α => map (Prod.mk x) ν
#align measure_theory.measure.prod MeasureTheory.Measure.prod

def FiniteSpanningSetsIn.prod {ν : Measure β} {C : Set (Set α)} {D : Set (Set β)}
    (hμ : μ.FiniteSpanningSetsIn C) (hν : ν.FiniteSpanningSetsIn D) :
    (μ.prod ν).FiniteSpanningSetsIn (image2 (· ×ˢ ·) C D) := by
  haveI := hν.sigmaFinite
  refine'
    ⟨fun n => hμ.set n.unpair.1 ×ˢ hν.set n.unpair.2, fun n =>
      mem_image2_of_mem (hμ.set_mem _) (hν.set_mem _), fun n => _, _⟩
  · rw [prod_prod]
    exact mul_lt_top (hμ.finite _).ne (hν.finite _).ne
  · simp_rw [iUnion_unpair_prod, hμ.spanning, hν.spanning, univ_prod_univ]
#align measure_theory.measure.finite_spanning_sets_in.prod MeasureTheory.Measure.FiniteSpanningSetsIn.prod

def fst (ρ : Measure (α × β)) : Measure α :=
  ρ.map Prod.fst
#align measure_theory.measure.fst MeasureTheory.Measure.fst

def snd (ρ : Measure (α × β)) : Measure β :=
  ρ.map Prod.snd
#align measure_theory.measure.snd MeasureTheory.Measure.snd