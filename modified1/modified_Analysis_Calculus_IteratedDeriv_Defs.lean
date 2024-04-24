def iteratedDeriv (n : ℕ) (f : 𝕜 → F) (x : 𝕜) : F :=
  (iteratedFDeriv 𝕜 n f x : (Fin n → 𝕜) → F) fun _ : Fin n => 1
#align iterated_deriv iteratedDeriv

def iteratedDerivWithin (n : ℕ) (f : 𝕜 → F) (s : Set 𝕜) (x : 𝕜) : F :=
  (iteratedFDerivWithin 𝕜 n f s x : (Fin n → 𝕜) → F) fun _ : Fin n => 1
#align iterated_deriv_within iteratedDerivWithin