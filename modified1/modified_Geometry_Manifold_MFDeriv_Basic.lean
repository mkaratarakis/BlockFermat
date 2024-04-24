structure as they are
necessary in lemmas mentioning the derivative, but not in lemmas about differentiability, so we
want to include them or omit them when necessary. -/
variable [Is : SmoothManifoldWithCorners I M] [I's : SmoothManifoldWithCorners I' M']
  [I''s : SmoothManifoldWithCorners I'' M'']
  {f' f₀' f₁' : TangentSpace I x →L[𝕜] TangentSpace I' (f x)}
  {g' : TangentSpace I' (f x) →L[𝕜] TangentSpace I'' (g (f x))}

/-- `UniqueMDiffWithinAt` achieves its goal: it implies the uniqueness of the derivative. -/
nonrec theorem UniqueMDiffWithinAt.eq (U : UniqueMDiffWithinAt I s x)
    (h : HasMFDerivWithinAt I I' f s x f') (h₁ : HasMFDerivWithinAt I I' f s x f₁') : f' = f₁' := by
  -- Porting note: didn't need `convert` because of finding instances by unification
  convert U.eq h.2 h₁.2
#align unique_mdiff_within_at.eq UniqueMDiffWithinAt.eq