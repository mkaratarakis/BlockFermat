def scaleRoots (p : R[X]) (s : R) : R[X] :=
  ∑ i in p.support, monomial i (p.coeff i * s ^ (p.natDegree - i))
#align polynomial.scale_roots Polynomial.scaleRoots