def orthogonal : Submodule 𝕜 E where
  carrier := { v | ∀ u ∈ K, ⟪u, v⟫ = 0 }
  zero_mem' _ _ := inner_zero_right _
  add_mem' hx hy u hu := by rw [inner_add_right, hx u hu, hy u hu, add_zero]
  smul_mem' c x hx u hu := by rw [inner_smul_right, hx u hu, mul_zero]
#align submodule.orthogonal Submodule.orthogonal

def IsOrtho (U V : Submodule 𝕜 E) : Prop :=
  U ≤ Vᗮ
#align submodule.is_ortho Submodule.IsOrtho