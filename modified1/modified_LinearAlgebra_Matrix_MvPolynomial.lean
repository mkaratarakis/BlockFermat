def mvPolynomialX [CommSemiring R] : Matrix m n (MvPolynomial (m × n) R) :=
  of fun i j => MvPolynomial.X (i, j)
#align matrix.mv_polynomial_X Matrix.mvPolynomialX