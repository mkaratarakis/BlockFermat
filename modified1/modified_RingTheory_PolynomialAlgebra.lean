def matPolyEquiv :
    Matrix n n R[X] ≃ₐ[R] (Matrix n n R)[X]
```
which is characterized by
```
coeff (matPolyEquiv m) k i j = coeff (m i j) k
```

We will use this algebra isomorphism to prove the Cayley-Hamilton theorem.
-/

universe u v w

open Polynomial TensorProduct

open Algebra.TensorProduct (algHomOfLinearMapTensorProduct includeLeft)

noncomputable section

variable (R A : Type*)
variable [CommSemiring R]
variable [Semiring A] [Algebra R A]

namespace PolyEquivTensor

/-- (Implementation detail).
The function underlying `A ⊗[R] R[X] →ₐ[R] A[X]`,
as a bilinear function of two arguments.
-/
-- Porting note: was  `@[simps apply_apply]`
@[simps! apply_apply]
def toFunBilinear : A →ₗ[A] R[X] →ₗ[R] A[X] :=
  LinearMap.toSpanSingleton A _ (aeval (Polynomial.X : A[X])).toLinearMap
#align poly_equiv_tensor.to_fun_bilinear PolyEquivTensor.toFunBilinear

def toFunLinear : A ⊗[R] R[X] →ₗ[R] A[X] :=
  TensorProduct.lift (toFunBilinear R A)
#align poly_equiv_tensor.to_fun_linear PolyEquivTensor.toFunLinear

def toFunAlgHom : A ⊗[R] R[X] →ₐ[R] A[X] :=
  algHomOfLinearMapTensorProduct (toFunLinear R A) (toFunLinear_mul_tmul_mul R A)
    (toFunLinear_one_tmul_one R A)
#align poly_equiv_tensor.to_fun_alg_hom PolyEquivTensor.toFunAlgHom

def invFun (p : A[X]) : A ⊗[R] R[X] :=
  p.eval₂ (includeLeft : A →ₐ[R] A ⊗[R] R[X]) ((1 : A) ⊗ₜ[R] (X : R[X]))
#align poly_equiv_tensor.inv_fun PolyEquivTensor.invFun

def equiv : A ⊗[R] R[X] ≃ A[X] where
  toFun := toFunAlgHom R A
  invFun := invFun R A
  left_inv := left_inv R A
  right_inv := right_inv R A
#align poly_equiv_tensor.equiv PolyEquivTensor.equiv

def polyEquivTensor : A[X] ≃ₐ[R] A ⊗[R] R[X] :=
  AlgEquiv.symm { PolyEquivTensor.toFunAlgHom R A, PolyEquivTensor.equiv R A with }
#align poly_equiv_tensor polyEquivTensor

def matPolyEquiv : Matrix n n R[X] ≃ₐ[R] (Matrix n n R)[X] :=
  ((matrixEquivTensor R R[X] n).trans (Algebra.TensorProduct.comm R _ _)).trans
    (polyEquivTensor R (Matrix n n R)).symm
#align mat_poly_equiv matPolyEquiv