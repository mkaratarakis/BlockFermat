def vars (p : MvPolynomial σ R) : Finset σ :=
  letI := Classical.decEq σ
  p.degrees.toFinset
#align mv_polynomial.vars MvPolynomial.vars

def [DecidableEq σ] (p : MvPolynomial σ R) : p.vars = p.degrees.toFinset := by
  rw [vars]
  convert rfl
#align mv_polynomial.vars_def MvPolynomial.vars_def