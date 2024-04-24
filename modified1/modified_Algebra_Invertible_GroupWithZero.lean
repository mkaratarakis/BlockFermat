def invertibleOfNonzero {a : α} (h : a ≠ 0) : Invertible a :=
  ⟨a⁻¹, inv_mul_cancel h, mul_inv_cancel h⟩
#align invertible_of_nonzero invertibleOfNonzero

def invertibleInv {a : α} [Invertible a] : Invertible a⁻¹ :=
  ⟨a, by simp, by simp⟩
#align invertible_inv invertibleInv