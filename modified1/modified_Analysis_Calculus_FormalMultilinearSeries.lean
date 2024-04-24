def FormalMultilinearSeries (𝕜 : Type*) (E : Type*) (F : Type*) [Ring 𝕜] [AddCommGroup E]
    [Module 𝕜 E] [TopologicalSpace E] [TopologicalAddGroup E] [ContinuousConstSMul 𝕜 E]
    [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [TopologicalAddGroup F]
    [ContinuousConstSMul 𝕜 F] :=
  ∀ n : ℕ, E[×n]→L[𝕜] F
#align formal_multilinear_series FormalMultilinearSeries

def prod (p : FormalMultilinearSeries 𝕜 E F) (q : FormalMultilinearSeries 𝕜 E G) :
    FormalMultilinearSeries 𝕜 E (F × G)
  | n => (p n).prod (q n)

/-- Killing the zeroth coefficient in a formal multilinear series -/
def removeZero (p : FormalMultilinearSeries 𝕜 E F) : FormalMultilinearSeries 𝕜 E F
  | 0 => 0
  | n + 1 => p (n + 1)
#align formal_multilinear_series.remove_zero FormalMultilinearSeries.removeZero

def compContinuousLinearMap (p : FormalMultilinearSeries 𝕜 F G) (u : E →L[𝕜] F) :
    FormalMultilinearSeries 𝕜 E G := fun n => (p n).compContinuousLinearMap fun _ : Fin n => u
#align formal_multilinear_series.comp_continuous_linear_map FormalMultilinearSeries.compContinuousLinearMap

def restrictScalars (p : FormalMultilinearSeries 𝕜' E F) :
    FormalMultilinearSeries 𝕜 E F := fun n => (p n).restrictScalars 𝕜
#align formal_multilinear_series.restrict_scalars FormalMultilinearSeries.restrictScalars

def shift : FormalMultilinearSeries 𝕜 E (E →L[𝕜] F) := fun n => (p n.succ).curryRight
#align formal_multilinear_series.shift FormalMultilinearSeries.shift

def unshift (q : FormalMultilinearSeries 𝕜 E (E →L[𝕜] F)) (z : F) : FormalMultilinearSeries 𝕜 E F
  | 0 => (continuousMultilinearCurryFin0 𝕜 E F).symm z
  | n + 1 => -- Porting note: added type hint here and explicit universes to fix compile
    (continuousMultilinearCurryRightEquiv' 𝕜 n E F :
      (E [×n]→L[𝕜] E →L[𝕜] F) → (E [×n.succ]→L[𝕜] F)) (q n)
#align formal_multilinear_series.unshift FormalMultilinearSeries.unshift

def compFormalMultilinearSeries (f : F →L[𝕜] G) (p : FormalMultilinearSeries 𝕜 E F) :
    FormalMultilinearSeries 𝕜 E G := fun n => f.compContinuousMultilinearMap (p n)
#align continuous_linear_map.comp_formal_multilinear_series ContinuousLinearMap.compFormalMultilinearSeries

def toFormalMultilinearSeries : FormalMultilinearSeries 𝕜 (∀ i, E i) F :=
  fun n ↦ if h : Fintype.card ι = n then
    (f.compContinuousLinearMap .proj).domDomCongr (Fintype.equivFinOfCardEq h)
  else 0

end ContinuousMultilinearMap

end

namespace FormalMultilinearSeries

section Order

variable [Ring 𝕜] {n : ℕ} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [TopologicalAddGroup E] [ContinuousConstSMul 𝕜 E] [AddCommGroup F] [Module 𝕜 F]
  [TopologicalSpace F] [TopologicalAddGroup F] [ContinuousConstSMul 𝕜 F]
  {p : FormalMultilinearSeries 𝕜 E F}

/-- The index of the first non-zero coefficient in `p` (or `0` if all coefficients are zero). This
  is the order of the isolated zero of an analytic function `f` at a point if `p` is the Taylor
  series of `f` at that point. -/
noncomputable def order (p : FormalMultilinearSeries 𝕜 E F) : ℕ :=
  sInf { n | p n ≠ 0 }
#align formal_multilinear_series.order FormalMultilinearSeries.order

def hp
#align formal_multilinear_series.order_eq_find FormalMultilinearSeries.order_eq_find

def coeff (p : FormalMultilinearSeries 𝕜 𝕜 E) (n : ℕ) : E :=
  p n 1
#align formal_multilinear_series.coeff FormalMultilinearSeries.coeff

def fslope (p : FormalMultilinearSeries 𝕜 𝕜 E) : FormalMultilinearSeries 𝕜 𝕜 E :=
  fun n => (p (n + 1)).curryLeft 1
#align formal_multilinear_series.fslope FormalMultilinearSeries.fslope

def constFormalMultilinearSeries (𝕜 : Type*) [NontriviallyNormedField 𝕜] (E : Type*)
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [ContinuousConstSMul 𝕜 E] [TopologicalAddGroup E]
    {F : Type*} [NormedAddCommGroup F] [TopologicalAddGroup F] [NormedSpace 𝕜 F]
    [ContinuousConstSMul 𝕜 F] (c : F) : FormalMultilinearSeries 𝕜 E F
  | 0 => ContinuousMultilinearMap.curry0 _ _ c
  | _ => 0
#align const_formal_multilinear_series constFormalMultilinearSeries

def fpowerSeries (f : E →L[𝕜] F) (x : E) : FormalMultilinearSeries 𝕜 E F
  | 0 => ContinuousMultilinearMap.curry0 𝕜 _ (f x)
  | 1 => (continuousMultilinearCurryFin1 𝕜 E F).symm f
  | _ => 0
#align continuous_linear_map.fpower_series ContinuousLinearMap.fpowerSeries