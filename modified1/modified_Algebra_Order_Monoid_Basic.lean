def Function.Injective.orderedCommMonoid [OrderedCommMonoid α] {β : Type*} [One β] [Mul β]
    [Pow β ℕ] (f : β → α) (hf : Function.Injective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) :
    OrderedCommMonoid β where
  toCommMonoid := hf.commMonoid f one mul npow
  toPartialOrder := PartialOrder.lift f hf
  mul_le_mul_left a b ab c := show f (c * a) ≤ f (c * b) by
    rw [mul, mul]; apply mul_le_mul_left'; exact ab
#align function.injective.ordered_comm_monoid Function.Injective.orderedCommMonoid

def Function.Injective.orderedCancelCommMonoid [OrderedCancelCommMonoid α] [One β] [Mul β] [Pow β ℕ]
    (f : β → α) (hf : Injective f) (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) : OrderedCancelCommMonoid β where
  toOrderedCommMonoid := hf.orderedCommMonoid f one mul npow
  le_of_mul_le_mul_left a b c (bc : f (a * b) ≤ f (a * c)) :=
    (mul_le_mul_iff_left (f a)).1 (by rwa [← mul, ← mul])
#align function.injective.ordered_cancel_comm_monoid Function.Injective.orderedCancelCommMonoid

def Function.Injective.linearOrderedCommMonoid [LinearOrderedCommMonoid α] {β : Type*} [One β]
    [Mul β] [Pow β ℕ] [Sup β] [Inf β] (f : β → α) (hf : Function.Injective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (sup : ∀ x y, f (x ⊔ y) = max (f x) (f y)) (inf : ∀ x y, f (x ⊓ y) = min (f x) (f y)) :
    LinearOrderedCommMonoid β where
  toOrderedCommMonoid := hf.orderedCommMonoid f one mul npow
  __ := LinearOrder.lift f hf sup inf
#align function.injective.linear_ordered_comm_monoid Function.Injective.linearOrderedCommMonoid

def Function.Injective.linearOrderedCancelCommMonoid [LinearOrderedCancelCommMonoid α] [One β]
    [Mul β] [Pow β ℕ] [Sup β] [Inf β] (f : β → α) (hf : Injective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (hsup : ∀ x y, f (x ⊔ y) = max (f x) (f y)) (hinf : ∀ x y, f (x ⊓ y) = min (f x) (f y)) :
    LinearOrderedCancelCommMonoid β where
  toOrderedCancelCommMonoid := hf.orderedCancelCommMonoid f one mul npow
  __ := hf.linearOrderedCommMonoid f one mul npow hsup hinf
#align function.injective.linear_ordered_cancel_comm_monoid Function.Injective.linearOrderedCancelCommMonoid

def OrderEmbedding.mulLeft {α : Type*} [Mul α] [LinearOrder α]
    [CovariantClass α α (· * ·) (· < ·)] (m : α) : α ↪o α :=
  OrderEmbedding.ofStrictMono (fun n => m * n) fun _ _ w => mul_lt_mul_left' w m
#align order_embedding.mul_left OrderEmbedding.mulLeft

def OrderEmbedding.mulRight {α : Type*} [Mul α] [LinearOrder α]
    [CovariantClass α α (swap (· * ·)) (· < ·)] (m : α) : α ↪o α :=
  OrderEmbedding.ofStrictMono (fun n => n * m) fun _ _ w => mul_lt_mul_right' w m
#align order_embedding.mul_right OrderEmbedding.mulRight