def expand : R[X] →ₐ[R] R[X] :=
  { (eval₂RingHom C (X ^ p) : R[X] →+* R[X]) with commutes' := fun _ => eval₂_C _ _ }
#align polynomial.expand Polynomial.expand

def contract (p : ℕ) (f : R[X]) : R[X] :=
  ∑ n in range (f.natDegree + 1), monomial n (f.coeff (n * p))
#align polynomial.contract Polynomial.contract