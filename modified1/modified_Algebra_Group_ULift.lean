def _root_.MulEquiv.ulift [Mul α] : ULift α ≃* α :=
  { Equiv.ulift with map_mul' := fun _ _ => rfl }
#align mul_equiv.ulift MulEquiv.ulift