def Contravariant.toLeftCancelSemigroup [ContravariantClass α α (· * ·) (· ≤ ·)] :
    LeftCancelSemigroup α :=
  { ‹Semigroup α› with mul_left_cancel := fun a b c => mul_left_cancel'' }
#align contravariant.to_left_cancel_semigroup Contravariant.toLeftCancelSemigroup

def Contravariant.toRightCancelSemigroup [ContravariantClass α α (swap (· * ·)) (· ≤ ·)] :
    RightCancelSemigroup α :=
  { ‹Semigroup α› with mul_right_cancel := fun a b c => mul_right_cancel'' }
#align contravariant.to_right_cancel_semigroup Contravariant.toRightCancelSemigroup

def MulLECancellable [Mul α] [LE α] (a : α) : Prop :=
  ∀ ⦃b c⦄, a * b ≤ a * c → b ≤ c
#align mul_le_cancellable MulLECancellable