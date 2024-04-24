def ker (f : F) : Submodule R M :=
  comap f ⊥
#align linear_map.ker LinearMap.ker

def iterateKer (f : M →ₗ[R] M) : ℕ →o Submodule R M where
  toFun n := ker (f ^ n)
  monotone' n m w x h := by
    obtain ⟨c, rfl⟩ := le_iff_exists_add.mp w
    rw [LinearMap.mem_ker] at h
    rw [LinearMap.mem_ker, add_comm, pow_add, LinearMap.mul_apply, h, LinearMap.map_zero]
#align linear_map.iterate_ker LinearMap.iterateKer