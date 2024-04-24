def IdemSemiring.ofSemiring [Semiring α] (h : ∀ a : α, a + a = a) : IdemSemiring α :=
  { ‹Semiring α› with
    le := fun a b ↦ a + b = b
    le_refl := h
    le_trans := fun a b c hab hbc ↦ by
      simp only
      rw [← hbc, ← add_assoc, hab]
    le_antisymm := fun a b hab hba ↦ by rwa [← hba, add_comm]
    sup := (· + ·)
    le_sup_left := fun a b ↦ by
      simp only
      rw [← add_assoc, h]
    le_sup_right := fun a b ↦ by
      simp only
      rw [add_comm, add_assoc, h]
    sup_le := fun a b c hab hbc ↦ by
      simp only
      rwa [add_assoc, hbc]
    bot := 0
    bot_le := zero_add }
#align idem_semiring.of_semiring IdemSemiring.ofSemiring

def (a : α × β) : a∗ = (a.1∗, a.2∗) :=
  rfl
#align prod.kstar_def Prod.kstar_def

def (a : ∀ i, π i) : a∗ = fun i ↦ (a i)∗ :=
  rfl
#align pi.kstar_def Pi.kstar_def

def idemSemiring [IdemSemiring α] [Zero β] [One β] [Add β] [Mul β] [Pow β ℕ] [SMul ℕ β]
    [NatCast β] [Sup β] [Bot β] (f : β → α) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (nat_cast : ∀ n : ℕ, f n = n) (sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (bot : f ⊥ = ⊥) :
    IdemSemiring β :=
  { hf.semiring f zero one add mul nsmul npow nat_cast, hf.semilatticeSup _ sup,
    ‹Bot β› with
    add_eq_sup := fun a b ↦ hf <| by erw [sup, add, add_eq_sup]
    bot := ⊥
    bot_le := fun a ↦ bot.trans_le <| @bot_le _ _ _ <| f a }
#align function.injective.idem_semiring Function.Injective.idemSemiring

def idemCommSemiring [IdemCommSemiring α] [Zero β] [One β] [Add β] [Mul β] [Pow β ℕ]
    [SMul ℕ β] [NatCast β] [Sup β] [Bot β] (f : β → α) (hf : Injective f) (zero : f 0 = 0)
    (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (nat_cast : ∀ n : ℕ, f n = n) (sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (bot : f ⊥ = ⊥) :
    IdemCommSemiring β :=
  { hf.commSemiring f zero one add mul nsmul npow nat_cast,
    hf.idemSemiring f zero one add mul nsmul npow nat_cast sup bot with }
#align function.injective.idem_comm_semiring Function.Injective.idemCommSemiring

def kleeneAlgebra [KleeneAlgebra α] [Zero β] [One β] [Add β] [Mul β] [Pow β ℕ] [SMul ℕ β]
    [NatCast β] [Sup β] [Bot β] [KStar β] (f : β → α) (hf : Injective f) (zero : f 0 = 0)
    (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (nat_cast : ∀ n : ℕ, f n = n) (sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (bot : f ⊥ = ⊥)
    (kstar : ∀ a, f a∗ = (f a)∗) : KleeneAlgebra β :=
  { hf.idemSemiring f zero one add mul nsmul npow nat_cast sup bot,
    ‹KStar β› with
    one_le_kstar := fun a ↦ one.trans_le <| by
      erw [kstar]
      exact one_le_kstar
    mul_kstar_le_kstar := fun a ↦ by
      change f _ ≤ _
      erw [mul, kstar]
      exact mul_kstar_le_kstar
    kstar_mul_le_kstar := fun a ↦ by
      change f _ ≤ _
      erw [mul, kstar]
      exact kstar_mul_le_kstar
    mul_kstar_le_self := fun a b (h : f _ ≤ _) ↦ by
      change f _ ≤ _
      erw [mul, kstar]
      erw [mul] at h
      exact mul_kstar_le_self h
    kstar_mul_le_self := fun a b (h : f _ ≤ _) ↦ by
      change f _ ≤ _
      erw [mul, kstar]
      erw [mul] at h
      exact kstar_mul_le_self h }
#align function.injective.kleene_algebra Function.Injective.kleeneAlgebra