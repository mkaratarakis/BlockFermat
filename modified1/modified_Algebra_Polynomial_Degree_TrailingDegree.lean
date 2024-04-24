def trailingDegree (p : R[X]) : ℕ∞ :=
  p.support.min
#align polynomial.trailing_degree Polynomial.trailingDegree

def natTrailingDegree (p : R[X]) : ℕ :=
  (trailingDegree p).getD 0
#align polynomial.nat_trailing_degree Polynomial.natTrailingDegree

def trailingCoeff (p : R[X]) : R :=
  coeff p (natTrailingDegree p)
#align polynomial.trailing_coeff Polynomial.trailingCoeff

def TrailingMonic (p : R[X]) :=
  trailingCoeff p = (1 : R)
#align polynomial.trailing_monic Polynomial.TrailingMonic

def : TrailingMonic p ↔ trailingCoeff p = 1 :=
  Iff.rfl
#align polynomial.trailing_monic.def Polynomial.TrailingMonic.def

def nextCoeffUp (p : R[X]) : R :=
  if p.natTrailingDegree = 0 then 0 else p.coeff (p.natTrailingDegree + 1)
#align polynomial.next_coeff_up Polynomial.nextCoeffUp