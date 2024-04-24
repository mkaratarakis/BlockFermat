def toUnits [Group G] : G ≃* Gˣ where
  toFun x := ⟨x, x⁻¹, mul_inv_self _, inv_mul_self _⟩
  invFun x := x
  left_inv _ := rfl
  right_inv _ := Units.ext rfl
  map_mul' _ _ := Units.ext rfl
#align to_units toUnits

def mapEquiv (h : M ≃* N) : Mˣ ≃* Nˣ :=
  { map h.toMonoidHom with
    invFun := map h.symm.toMonoidHom,
    left_inv := fun u => ext <| h.left_inv u,
    right_inv := fun u => ext <| h.right_inv u }
#align units.map_equiv Units.mapEquiv

def mulLeft (u : Mˣ) : Equiv.Perm M where
  toFun x := u * x
  invFun x := u⁻¹ * x
  left_inv := u.inv_mul_cancel_left
  right_inv := u.mul_inv_cancel_left
#align units.mul_left Units.mulLeft

def mulRight (u : Mˣ) : Equiv.Perm M where
  toFun x := x * u
  invFun x := x * ↑u⁻¹
  left_inv x := mul_inv_cancel_right x u
  right_inv x := inv_mul_cancel_right x u
#align units.mul_right Units.mulRight

def mulLeft (a : G) : Perm G :=
  (toUnits a).mulLeft
#align equiv.mul_left Equiv.mulLeft

def mulRight (a : G) : Perm G :=
  (toUnits a).mulRight
#align equiv.mul_right Equiv.mulRight

def divLeft (a : G) : G ≃ G where
  toFun b := a / b
  invFun b := b⁻¹ * a
  left_inv b := by simp [div_eq_mul_inv]
  right_inv b := by simp [div_eq_mul_inv]
#align equiv.div_left Equiv.divLeft

def divRight (a : G) : G ≃ G where
  toFun b := b / a
  invFun b := b * a
  left_inv b := by simp [div_eq_mul_inv]
  right_inv b := by simp [div_eq_mul_inv]
#align equiv.div_right Equiv.divRight

def MulEquiv.inv (G : Type*) [DivisionCommMonoid G] : G ≃* G :=
  { Equiv.inv G with toFun := Inv.inv, invFun := Inv.inv, map_mul' := mul_inv }
#align mul_equiv.inv MulEquiv.inv