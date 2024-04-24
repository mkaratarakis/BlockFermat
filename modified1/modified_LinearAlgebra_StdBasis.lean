def stdBasis : ∀ i : ι, φ i →ₗ[R] ∀ i, φ i :=
  single
#align linear_map.std_basis LinearMap.stdBasis

def basis (s : ∀ j, Basis (ιs j) R (Ms j)) :
    Basis (Σj, ιs j) R (∀ j, Ms j) :=
  Basis.ofRepr
    ((LinearEquiv.piCongrRight fun j => (s j).repr) ≪≫ₗ
      (Finsupp.sigmaFinsuppLEquivPiFinsupp R).symm)
  --  Porting note: was
  -- -- The `AddCommMonoid (Π j, Ms j)` instance was hard to find.
  -- -- Defining this in tactic mode seems to shake up instance search enough
  -- -- that it works by itself.
  -- refine Basis.ofRepr (?_ ≪≫ₗ (Finsupp.sigmaFinsuppLEquivPiFinsupp R).symm)
  -- exact LinearEquiv.piCongrRight fun j => (s j).repr
#align pi.basis Pi.basis

def basisFun : Basis η R (η → R) :=
  Basis.ofEquivFun (LinearEquiv.refl _ _)
#align pi.basis_fun Pi.basisFun

def piEquiv : (ι → M) ≃ₗ[R] ((ι → R) →ₗ[R] M) := Basis.constr (Pi.basisFun R ι) R

lemma piEquiv_apply_apply (ι R M : Type*) [Fintype ι] [CommSemiring R]
    [AddCommMonoid M] [Module R M] (v : ι → M) (w : ι → R) :
    piEquiv ι R M v w = ∑ i, w i • v i := by
  simp only [piEquiv, Basis.constr_apply_fintype, Basis.equivFun_apply]
  congr

@[simp] lemma range_piEquiv (v : ι → M) :
    LinearMap.range (piEquiv ι R M v) = span R (range v) :=
  Basis.constr_range _ _

@[simp] lemma surjective_piEquiv_apply_iff (v : ι → M) :
    Surjective (piEquiv ι R M v) ↔ span R (range v) = ⊤ := by
  rw [← LinearMap.range_eq_top, range_piEquiv]

end Module

namespace Matrix

variable (R : Type*) (m n : Type*) [Fintype m] [Finite n] [Semiring R]

/-- The standard basis of `Matrix m n R`. -/
noncomputable def stdBasis : Basis (m × n) R (Matrix m n R) :=
  Basis.reindex (Pi.basis fun _ : m => Pi.basisFun R n) (Equiv.sigmaEquivProd _ _)
#align matrix.std_basis Matrix.stdBasis