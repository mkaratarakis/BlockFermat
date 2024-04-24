def integralNormalization (f : R[X]) : R[X] :=
  ∑ i in f.support,
    monomial i (if f.degree = i then 1 else coeff f i * f.leadingCoeff ^ (f.natDegree - 1 - i))
#align polynomial.integral_normalization Polynomial.integralNormalization