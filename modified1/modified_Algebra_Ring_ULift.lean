def ringEquiv [NonUnitalNonAssocSemiring α] : ULift α ≃+* α where
  toFun := ULift.down
  invFun := ULift.up
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
#align ulift.ring_equiv ULift.ringEquiv