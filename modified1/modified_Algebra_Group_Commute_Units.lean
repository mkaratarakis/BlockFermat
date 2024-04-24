def Units.leftOfMul (u : Mˣ) (a b : M) (hu : a * b = u) (hc : Commute a b) : Mˣ where
  val := a
  inv := b * ↑u⁻¹
  val_inv := by rw [← mul_assoc, hu, u.mul_inv]
  inv_val := by
    have : Commute a u := hu ▸ (Commute.refl _).mul_right hc
    rw [← this.units_inv_right.right_comm, ← hc.eq, hu, u.mul_inv]
#align units.left_of_mul Units.leftOfMul

def Units.rightOfMul (u : Mˣ) (a b : M) (hu : a * b = u) (hc : Commute a b) : Mˣ :=
  u.leftOfMul b a (hc.eq ▸ hu) hc.symm
#align units.right_of_mul Units.rightOfMul

def Units.ofPow (u : Mˣ) (x : M) {n : ℕ} (hn : n ≠ 0) (hu : x ^ n = u) : Mˣ :=
  u.leftOfMul x (x ^ (n - 1))
    (by rwa [← _root_.pow_succ', Nat.sub_add_cancel (Nat.succ_le_of_lt <| Nat.pos_of_ne_zero hn)])
    (Commute.self_pow _ _)
#align units.of_pow Units.ofPow

def Units.ofPowEqOne (a : M) (n : ℕ) (ha : a ^ n = 1) (hn : n ≠ 0) : Mˣ := Units.ofPow 1 a hn ha
#align units.of_pow_eq_one Units.ofPowEqOne