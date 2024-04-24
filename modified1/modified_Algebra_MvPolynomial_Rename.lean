def rename (f : σ → τ) : MvPolynomial σ R →ₐ[R] MvPolynomial τ R :=
  aeval (X ∘ f)
#align mv_polynomial.rename MvPolynomial.rename

def killCompl : MvPolynomial τ R →ₐ[R] MvPolynomial σ R :=
  aeval fun i => if h : i ∈ Set.range f then X <| (Equiv.ofInjective f hf).symm ⟨i, h⟩ else 0
#align mv_polynomial.kill_compl MvPolynomial.killCompl

def renameEquiv (f : σ ≃ τ) : MvPolynomial σ R ≃ₐ[R] MvPolynomial τ R :=
  { rename f with
    toFun := rename f
    invFun := rename f.symm
    left_inv := fun p => by rw [rename_rename, f.symm_comp_self, rename_id]
    right_inv := fun p => by rw [rename_rename, f.self_comp_symm, rename_id] }
#align mv_polynomial.rename_equiv MvPolynomial.renameEquiv