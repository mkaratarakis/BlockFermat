def detRowAlternating : (n → R) [⋀^n]→ₗ[R] R :=
  MultilinearMap.alternatization ((MultilinearMap.mkPiAlgebra R n R).compLinearMap LinearMap.proj)
#align matrix.det_row_alternating Matrix.detRowAlternating

def detMonoidHom : Matrix n n R →* R where
  toFun := det
  map_one' := det_one
  map_mul' := det_mul
#align matrix.det_monoid_hom Matrix.detMonoidHom