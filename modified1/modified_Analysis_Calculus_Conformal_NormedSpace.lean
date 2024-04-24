def ConformalAt (f : X → Y) (x : X) :=
  ∃ f' : X →L[ℝ] Y, HasFDerivAt f f' x ∧ IsConformalMap f'
#align conformal_at ConformalAt

def Conformal (f : X → Y) :=
  ∀ x : X, ConformalAt f x
#align conformal Conformal