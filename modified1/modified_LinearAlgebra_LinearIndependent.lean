def LinearIndependent : Prop :=
  LinearMap.ker (Finsupp.total ι M R v) = ⊥
#align linear_independent LinearIndependent

def delabLinearIndependent : Delab :=
  whenPPOption getPPNotation <|
  whenNotPPOption getPPAnalysisSkip <|
  withOptionAtCurrPos `pp.analysis.skip true do
    let e ← getExpr
    guard <| e.isAppOfArity ``LinearIndependent 7
    let some _ := (e.getArg! 0).coeTypeSet? | failure
    let optionsPerPos ← if (e.getArg! 3).isLambda then
      withNaryArg 3 do return (← read).optionsPerPos.setBool (← getPos) pp.funBinderTypes.name true
    else
      withNaryArg 0 do return (← read).optionsPerPos.setBool (← getPos) `pp.analysis.namedArg true
    withTheReader Context ({· with optionsPerPos}) delab

variable {R} {v}

theorem linearIndependent_iff : LinearIndependent R v ↔ ∀ l, Finsupp.total ι M R v l = 0 → l = 0 :=
  by simp [LinearIndependent, LinearMap.ker_eq_bot']
#align linear_independent_iff linearIndependent_iff

def LinearIndependent.Maximal {ι : Type w} {R : Type u} [Semiring R] {M : Type v} [AddCommMonoid M]
    [Module R M] {v : ι → M} (_i : LinearIndependent R v) : Prop :=
  ∀ (s : Set M) (_i' : LinearIndependent R ((↑) : s → M)) (_h : range v ≤ s), range v = s
#align linear_independent.maximal LinearIndependent.Maximal

def LinearIndependent.totalEquiv (hv : LinearIndependent R v) :
    (ι →₀ R) ≃ₗ[R] span R (range v) := by
  apply LinearEquiv.ofBijective (LinearMap.codRestrict (span R (range v)) (Finsupp.total ι M R v) _)
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_codRestrict]
    apply hv
    · intro l
      rw [← Finsupp.range_total]
      rw [LinearMap.mem_range]
      apply mem_range_self l
  · rw [← LinearMap.range_eq_top, LinearMap.range_eq_map, LinearMap.map_codRestrict, ←
      LinearMap.range_le_iff_comap, range_subtype, Submodule.map_top]
    rw [Finsupp.range_total]
#align linear_independent.total_equiv LinearIndependent.totalEquiv

def LinearIndependent.repr (hv : LinearIndependent R v) : span R (range v) →ₗ[R] ι →₀ R :=
  hv.totalEquiv.symm
#align linear_independent.repr LinearIndependent.repr

def LinearIndependent.extend (hs : LinearIndependent K (fun x => x : s → V))
    (hst : s ⊆ t) : Set V :=
  Classical.choose (exists_linearIndependent_extension hs hst)
#align linear_independent.extend LinearIndependent.extend