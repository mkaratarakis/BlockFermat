def trace (A : Matrix n n R) : R :=
  ∑ i, diag A i
#align matrix.trace Matrix.trace

def traceAddMonoidHom : Matrix n n R →+ R where
  toFun := trace
  map_zero' := trace_zero n R
  map_add' := trace_add
#align matrix.trace_add_monoid_hom Matrix.traceAddMonoidHom

def traceLinearMap [Semiring α] [Module α R] : Matrix n n R →ₗ[α] R where
  toFun := trace
  map_add' := trace_add
  map_smul' := trace_smul
#align matrix.trace_linear_map Matrix.traceLinearMap