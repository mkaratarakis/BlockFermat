structure for the type
`MvPolynomial σ R`.

This structure itself is provided elsewhere as `MvPolynomial.isScalarTower`

When you update this file, you can also try to make a corresponding update in
`RingTheory.Polynomial.Tower`.
-/


variable (R A B : Type*) {σ : Type*}

namespace MvPolynomial

section Semiring

variable [CommSemiring R] [CommSemiring A] [CommSemiring B]
variable [Algebra R A] [Algebra A B] [Algebra R B]
variable [IsScalarTower R A B]
variable {R B}

theorem aeval_map_algebraMap (x : σ → B) (p : MvPolynomial σ R) :
    aeval x (map (algebraMap R A) p) = aeval x p := by
  rw [aeval_def, aeval_def, eval₂_map, IsScalarTower.algebraMap_eq R A B]
#align mv_polynomial.aeval_map_algebra_map MvPolynomial.aeval_map_algebraMap