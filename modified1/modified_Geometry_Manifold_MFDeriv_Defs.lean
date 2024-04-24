def DifferentiableWithinAtProp (f : H → H') (s : Set H) (x : H) : Prop :=
  DifferentiableWithinAt 𝕜 (I' ∘ f ∘ I.symm) (I.symm ⁻¹' s ∩ Set.range I) (I x)
#align differentiable_within_at_prop DifferentiableWithinAtProp

def UniqueMDiffWithinAt (s : Set M) (x : M) :=
  UniqueDiffWithinAt 𝕜 ((extChartAt I x).symm ⁻¹' s ∩ range I) ((extChartAt I x) x)
#align unique_mdiff_within_at UniqueMDiffWithinAt

def UniqueMDiffOn (s : Set M) :=
  ∀ x ∈ s, UniqueMDiffWithinAt I s x
#align unique_mdiff_on UniqueMDiffOn

def MDifferentiableWithinAt (f : M → M') (s : Set M) (x : M) :=
  ContinuousWithinAt f s x ∧
    DifferentiableWithinAt 𝕜 (writtenInExtChartAt I I' x f) ((extChartAt I x).symm ⁻¹' s ∩ range I)
      ((extChartAt I x) x)
#align mdifferentiable_within_at MDifferentiableWithinAt

def MDifferentiableAt (f : M → M') (x : M) :=
  ContinuousAt f x ∧
    DifferentiableWithinAt 𝕜 (writtenInExtChartAt I I' x f) (range I) ((extChartAt I x) x)
#align mdifferentiable_at MDifferentiableAt

def MDifferentiableOn (f : M → M') (s : Set M) :=
  ∀ x ∈ s, MDifferentiableWithinAt I I' f s x
#align mdifferentiable_on MDifferentiableOn

def MDifferentiable (f : M → M') :=
  ∀ x, MDifferentiableAt I I' f x
#align mdifferentiable MDifferentiable

def PartialHomeomorph.MDifferentiable (f : PartialHomeomorph M M') :=
  MDifferentiableOn I I' f f.source ∧ MDifferentiableOn I' I f.symm f.target
#align local_homeomorph.mdifferentiable PartialHomeomorph.MDifferentiable

def HasMFDerivWithinAt (f : M → M') (s : Set M) (x : M)
    (f' : TangentSpace I x →L[𝕜] TangentSpace I' (f x)) :=
  ContinuousWithinAt f s x ∧
    HasFDerivWithinAt (writtenInExtChartAt I I' x f : E → E') f'
      ((extChartAt I x).symm ⁻¹' s ∩ range I) ((extChartAt I x) x)
#align has_mfderiv_within_at HasMFDerivWithinAt

def HasMFDerivAt (f : M → M') (x : M) (f' : TangentSpace I x →L[𝕜] TangentSpace I' (f x)) :=
  ContinuousAt f x ∧
    HasFDerivWithinAt (writtenInExtChartAt I I' x f : E → E') f' (range I) ((extChartAt I x) x)
#align has_mfderiv_at HasMFDerivAt

def mfderivWithin (f : M → M') (s : Set M) (x : M) : TangentSpace I x →L[𝕜] TangentSpace I' (f x) :=
  if MDifferentiableWithinAt I I' f s x then
    (fderivWithin 𝕜 (writtenInExtChartAt I I' x f) ((extChartAt I x).symm ⁻¹' s ∩ range I)
        ((extChartAt I x) x) :
      _)
  else 0
#align mfderiv_within mfderivWithin

def mfderiv (f : M → M') (x : M) : TangentSpace I x →L[𝕜] TangentSpace I' (f x) :=
  if MDifferentiableAt I I' f x then
    (fderivWithin 𝕜 (writtenInExtChartAt I I' x f : E → E') (range I) ((extChartAt I x) x) : _)
  else 0
#align mfderiv mfderiv

def tangentMapWithin (f : M → M') (s : Set M) : TangentBundle I M → TangentBundle I' M' := fun p =>
  ⟨f p.1, (mfderivWithin I I' f s p.1 : TangentSpace I p.1 → TangentSpace I' (f p.1)) p.2⟩
#align tangent_map_within tangentMapWithin

def tangentMap (f : M → M') : TangentBundle I M → TangentBundle I' M' := fun p =>
  ⟨f p.1, (mfderiv I I' f p.1 : TangentSpace I p.1 → TangentSpace I' (f p.1)) p.2⟩
#align tangent_map tangentMap