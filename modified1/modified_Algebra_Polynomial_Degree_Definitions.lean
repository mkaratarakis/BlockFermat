def degree (p : R[X]) : WithBot ℕ :=
  p.support.max
#align polynomial.degree Polynomial.degree

def natDegree (p : R[X]) : ℕ :=
  (degree p).unbot' 0
#align polynomial.nat_degree Polynomial.natDegree

def leadingCoeff (p : R[X]) : R :=
  coeff p (natDegree p)
#align polynomial.leading_coeff Polynomial.leadingCoeff

def Monic (p : R[X]) :=
  leadingCoeff p = (1 : R)
#align polynomial.monic Polynomial.Monic

def : Monic p ↔ leadingCoeff p = 1 :=
  Iff.rfl
#align polynomial.monic.def Polynomial.Monic.def

def nextCoeff (p : R[X]) : R :=
  if p.natDegree = 0 then 0 else p.coeff (p.natDegree - 1)
#align polynomial.next_coeff Polynomial.nextCoeff

def degreeMonoidHom [Nontrivial R] : R[X] →* Multiplicative (WithBot ℕ)
    where
  toFun := degree
  map_one' := degree_one
  map_mul' _ _ := degree_mul
#align polynomial.degree_monoid_hom Polynomial.degreeMonoidHom

def leadingCoeffHom : R[X] →* R where
  toFun := leadingCoeff
  map_one' := by simp
  map_mul' := leadingCoeff_mul
#align polynomial.leading_coeff_hom Polynomial.leadingCoeffHom