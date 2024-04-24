def div (p q : R[X]) :=
  C (leadingCoeff q)⁻¹ * (p /ₘ (q * C (leadingCoeff q)⁻¹))
#align polynomial.div Polynomial.div

def mod (p q : R[X]) :=
  p %ₘ (q * C (leadingCoeff q)⁻¹)
#align polynomial.mod Polynomial.mod

def : p / q = C (leadingCoeff q)⁻¹ * (p /ₘ (q * C (leadingCoeff q)⁻¹)) :=
  rfl
#align polynomial.div_def Polynomial.div_def

def : p % q = p %ₘ (q * C (leadingCoeff q)⁻¹) := rfl
#align polynomial.mod_def Polynomial.mod_def