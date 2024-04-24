def mul : A →ₗ[R] A →ₗ[R] A :=
  LinearMap.mk₂ R (· * ·) add_mul smul_mul_assoc mul_add mul_smul_comm
#align linear_map.mul LinearMap.mul

def mul' : A ⊗[R] A →ₗ[R] A :=
  TensorProduct.lift (mul R A)
#align linear_map.mul' LinearMap.mul'

def mulLeft (a : A) : A →ₗ[R] A :=
  mul R A a
#align linear_map.mul_left LinearMap.mulLeft

def mulRight (a : A) : A →ₗ[R] A :=
  (mul R A).flip a
#align linear_map.mul_right LinearMap.mulRight

def mulLeftRight (ab : A × A) : A →ₗ[R] A :=
  (mulRight R ab.snd).comp (mulLeft R ab.fst)
#align linear_map.mul_left_right LinearMap.mulLeftRight

def _root_.NonUnitalAlgHom.lmul : A →ₙₐ[R] End R A :=
  { mul R A with
    map_mul' := by
      intro a b
      ext c
      exact mul_assoc a b c
    map_zero' := by
      ext a
      exact zero_mul a }
#align non_unital_alg_hom.lmul NonUnitalAlgHom.lmul

def _root_.Algebra.lmul : A →ₐ[R] End R A :=
  { LinearMap.mul R A with
    map_one' := by
      ext a
      exact one_mul a
    map_mul' := by
      intro a b
      ext c
      exact mul_assoc a b c
    map_zero' := by
      ext a
      exact zero_mul a
    commutes' := by
      intro r
      ext a
      exact (Algebra.smul_def r a).symm }
#align algebra.lmul Algebra.lmul