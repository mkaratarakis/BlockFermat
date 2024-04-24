structure for the type `R[X]`.

This structure itself is provided elsewhere as `Polynomial.isScalarTower`

When you update this file, you can also try to make a corresponding update in
`RingTheory.MvPolynomial.Tower`.
-/


open Polynomial

variable (R A B : Type*)

namespace Polynomial

section Semiring

variable [CommSemiring R] [CommSemiring A] [Semiring B]
variable [Algebra R A] [Algebra A B] [Algebra R B]
variable [IsScalarTower R A B]
variable {R B}

@[simp]
theorem aeval_map_algebraMap (x : B) (p : R[X]) : aeval x (map (algebraMap R A) p) = aeval x p := by
  rw [aeval_def, aeval_def, eval₂_map, IsScalarTower.algebraMap_eq R A B]
#align polynomial.aeval_map_algebra_map Polynomial.aeval_map_algebraMap