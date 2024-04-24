def indicator [CommRing K] (a : σ → K) : MvPolynomial σ K :=
  ∏ n, (1 - (X n - C (a n)) ^ (Fintype.card K - 1))
#align mv_polynomial.indicator MvPolynomial.indicator

def evalₗ [CommSemiring K] : MvPolynomial σ K →ₗ[K] (σ → K) → K where
  toFun p e := eval e p
  map_add' p q := by ext x; simp
  map_smul' a p := by ext e; simp
#align mv_polynomial.evalₗ MvPolynomial.evalₗ

def R [CommRing K] : Type u :=
  restrictDegree σ K (Fintype.card K - 1)
set_option linter.uppercaseLean3 false in
#align mv_polynomial.R MvPolynomial.R

def evalᵢ [CommRing K] : R σ K →ₗ[K] (σ → K) → K :=
  (evalₗ K σ).comp (restrictDegree σ K (Fintype.card K - 1)).subtype
#align mv_polynomial.evalᵢ MvPolynomial.evalᵢ