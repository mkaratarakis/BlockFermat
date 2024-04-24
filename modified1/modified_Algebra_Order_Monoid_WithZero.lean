def Function.Injective.linearOrderedCommMonoidWithZero {β : Type*} [Zero β] [One β] [Mul β]
    [Pow β ℕ] [Sup β] [Inf β] (f : β → α) (hf : Function.Injective f) (zero : f 0 = 0)
    (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (hsup : ∀ x y, f (x ⊔ y) = max (f x) (f y)) (hinf : ∀ x y, f (x ⊓ y) = min (f x) (f y)) :
    LinearOrderedCommMonoidWithZero β :=
  { LinearOrder.lift f hf hsup hinf, hf.orderedCommMonoid f one mul npow,
    hf.commMonoidWithZero f zero one mul npow with
    zero_le_one :=
      show f 0 ≤ f 1 by simp only [zero, one, LinearOrderedCommMonoidWithZero.zero_le_one] }
#align function.injective.linear_ordered_comm_monoid_with_zero Function.Injective.linearOrderedCommMonoidWithZero

def OrderIso.mulLeft₀' {a : α} (ha : a ≠ 0) : α ≃o α :=
  { Equiv.mulLeft₀ a ha with map_rel_iff' := mul_le_mul_left₀ ha }
#align order_iso.mul_left₀' OrderIso.mulLeft₀'

def OrderIso.mulRight₀' {a : α} (ha : a ≠ 0) : α ≃o α :=
  { Equiv.mulRight₀ a ha with map_rel_iff' := mul_le_mul_right₀ ha }
#align order_iso.mul_right₀' OrderIso.mulRight₀'

def orderedAddCommMonoid [OrderedAddCommMonoid α] (zero_le : ∀ a : α, 0 ≤ a) :
    OrderedAddCommMonoid (WithZero α) :=
  { WithZero.partialOrder, WithZero.addCommMonoid with
    add_le_add_left := @add_le_add_left _ _ _ (WithZero.covariantClass_add_le zero_le).. }
#align with_zero.ordered_add_comm_monoid WithZero.orderedAddCommMonoid