def esymm (s : Multiset R) (n : ℕ) : R :=
  ((s.powersetCard n).map Multiset.prod).sum
#align multiset.esymm Multiset.esymm

def IsSymmetric [CommSemiring R] (φ : MvPolynomial σ R) : Prop :=
  ∀ e : Perm σ, rename e φ = φ
#align mv_polynomial.is_symmetric MvPolynomial.IsSymmetric

def symmetricSubalgebra [CommSemiring R] : Subalgebra R (MvPolynomial σ R) where
  carrier := setOf IsSymmetric
  algebraMap_mem' r e := rename_C e r
  mul_mem' ha hb e := by rw [AlgHom.map_mul, ha, hb]
  add_mem' ha hb e := by rw [AlgHom.map_add, ha, hb]
#align mv_polynomial.symmetric_subalgebra MvPolynomial.symmetricSubalgebra

def renameSymmetricSubalgebra [CommSemiring R] (e : σ ≃ τ) :
    symmetricSubalgebra σ R ≃ₐ[R] symmetricSubalgebra τ R :=
  AlgEquiv.ofAlgHom
    (((rename e).comp (symmetricSubalgebra σ R).val).codRestrict _ <| fun x => x.2.rename e)
    (((rename e.symm).comp <| Subalgebra.val _).codRestrict _ <| fun x => x.2.rename e.symm)
    (AlgHom.ext <| fun p => Subtype.ext <| by simp)
    (AlgHom.ext <| fun p => Subtype.ext <| by simp)

section ElementarySymmetric

open Finset

variable (σ R) [CommSemiring R] [CommSemiring S] [Fintype σ] [Fintype τ]

/-- The `n`th elementary symmetric `MvPolynomial σ R`. -/
def esymm (n : ℕ) : MvPolynomial σ R :=
  ∑ t in powersetCard n univ, ∏ i in t, X i
#align mv_polynomial.esymm MvPolynomial.esymm