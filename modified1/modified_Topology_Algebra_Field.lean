def Subfield.topologicalClosure (K : Subfield α) : Subfield α :=
  { K.toSubring.topologicalClosure with
    carrier := _root_.closure (K : Set α)
    inv_mem' := fun x hx => by
      dsimp only at hx ⊢
      rcases eq_or_ne x 0 with (rfl | h)
      · rwa [inv_zero]
      · -- Porting note (#11215): TODO: Lean fails to find InvMemClass instance

def affineHomeomorph (a b : 𝕜) (h : a ≠ 0) : 𝕜 ≃ₜ 𝕜 where
  toFun x := a * x + b
  invFun y := (y - b) / a
  left_inv x := by
    simp only [add_sub_cancel_right]
    exact mul_div_cancel_left₀ x h
  right_inv y := by simp [mul_div_cancel₀ _ h]
#align affine_homeomorph affineHomeomorph