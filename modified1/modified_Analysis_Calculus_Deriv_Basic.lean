def HasDerivAtFilter (f : 𝕜 → F) (f' : F) (x : 𝕜) (L : Filter 𝕜) :=
  HasFDerivAtFilter f (smulRight (1 : 𝕜 →L[𝕜] 𝕜) f') x L
#align has_deriv_at_filter HasDerivAtFilter

def HasDerivWithinAt (f : 𝕜 → F) (f' : F) (s : Set 𝕜) (x : 𝕜) :=
  HasDerivAtFilter f f' x (𝓝[s] x)
#align has_deriv_within_at HasDerivWithinAt

def HasDerivAt (f : 𝕜 → F) (f' : F) (x : 𝕜) :=
  HasDerivAtFilter f f' x (𝓝 x)
#align has_deriv_at HasDerivAt

def HasStrictDerivAt (f : 𝕜 → F) (f' : F) (x : 𝕜) :=
  HasStrictFDerivAt f (smulRight (1 : 𝕜 →L[𝕜] 𝕜) f') x
#align has_strict_deriv_at HasStrictDerivAt

def derivWithin (f : 𝕜 → F) (s : Set 𝕜) (x : 𝕜) :=
  fderivWithin 𝕜 f s x 1
#align deriv_within derivWithin

def deriv (f : 𝕜 → F) (x : 𝕜) :=
  fderiv 𝕜 f x 1
#align deriv deriv