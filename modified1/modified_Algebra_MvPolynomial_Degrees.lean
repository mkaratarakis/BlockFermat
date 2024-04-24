def degrees (p : MvPolynomial σ R) : Multiset σ :=
  letI := Classical.decEq σ
  p.support.sup fun s : σ →₀ ℕ => toMultiset s
#align mv_polynomial.degrees MvPolynomial.degrees

def [DecidableEq σ] (p : MvPolynomial σ R) :
    p.degrees = p.support.sup fun s : σ →₀ ℕ => Finsupp.toMultiset s := by rw [degrees]; convert rfl
#align mv_polynomial.degrees_def MvPolynomial.degrees_def

def degreeOf (n : σ) (p : MvPolynomial σ R) : ℕ :=
  letI := Classical.decEq σ
  p.degrees.count n
#align mv_polynomial.degree_of MvPolynomial.degreeOf

def [DecidableEq σ] (n : σ) (p : MvPolynomial σ R) :
    p.degreeOf n = p.degrees.count n := by rw [degreeOf]; convert rfl
#align mv_polynomial.degree_of_def MvPolynomial.degreeOf_def

def totalDegree (p : MvPolynomial σ R) : ℕ :=
  p.support.sup fun s => s.sum fun _ e => e
#align mv_polynomial.total_degree MvPolynomial.totalDegree