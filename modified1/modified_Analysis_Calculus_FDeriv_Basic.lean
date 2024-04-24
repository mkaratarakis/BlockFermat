def HasFDerivWithinAt (f : E → F) (f' : E →L[𝕜] F) (s : Set E) (x : E) :=
  HasFDerivAtFilter f f' x (𝓝[s] x)
#align has_fderiv_within_at HasFDerivWithinAt

def HasFDerivAt (f : E → F) (f' : E →L[𝕜] F) (x : E) :=
  HasFDerivAtFilter f f' x (𝓝 x)
#align has_fderiv_at HasFDerivAt

def HasStrictFDerivAt (f : E → F) (f' : E →L[𝕜] F) (x : E) :=
  (fun p : E × E => f p.1 - f p.2 - f' (p.1 - p.2)) =o[𝓝 (x, x)] fun p : E × E => p.1 - p.2
#align has_strict_fderiv_at HasStrictFDerivAt

def DifferentiableWithinAt (f : E → F) (s : Set E) (x : E) :=
  ∃ f' : E →L[𝕜] F, HasFDerivWithinAt f f' s x
#align differentiable_within_at DifferentiableWithinAt

def DifferentiableAt (f : E → F) (x : E) :=
  ∃ f' : E →L[𝕜] F, HasFDerivAt f f' x
#align differentiable_at DifferentiableAt

def fderivWithin (f : E → F) (s : Set E) (x : E) : E →L[𝕜] F :=
  if 𝓝[s \ {x}] x = ⊥ then 0 else
  if h : ∃ f', HasFDerivWithinAt f f' s x then Classical.choose h else 0
#align fderiv_within fderivWithin

def fderiv (f : E → F) (x : E) : E →L[𝕜] F :=
  if h : ∃ f', HasFDerivAt f f' x then Classical.choose h else 0
#align fderiv fderiv

def DifferentiableOn (f : E → F) (s : Set E) :=
  ∀ x ∈ s, DifferentiableWithinAt 𝕜 f s x
#align differentiable_on DifferentiableOn

def Differentiable (f : E → F) :=
  ∀ x, DifferentiableAt 𝕜 f x
#align differentiable Differentiable

structure HasFDerivAtFilter (f : E → F) (f' : E →L[𝕜] F) (x : E) (L : Filter E) : Prop where
  of_isLittleO :: isLittleO : (fun x' => f x' - f x - f' (x' - x)) =o[L] fun x' => x' - x
#align has_fderiv_at_filter HasFDerivAtFilter