def revAtFun (N i : ℕ) : ℕ :=
  ite (i ≤ N) (N - i) i
#align polynomial.rev_at_fun Polynomial.revAtFun

def revAt (N : ℕ) : Function.Embedding ℕ ℕ
    where
  toFun i := ite (i ≤ N) (N - i) i
  inj' := revAtFun_inj
#align polynomial.rev_at Polynomial.revAt

def reflect (N : ℕ) : R[X] → R[X]
  | ⟨f⟩ => ⟨Finsupp.embDomain (revAt N) f⟩
#align polynomial.reflect Polynomial.reflect

def reverse (f : R[X]) : R[X] :=
  reflect f.natDegree f
#align polynomial.reverse Polynomial.reverse