def distrib [Distrib α] (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) : Distrib β where
  left_distrib x y z := hf <| by simp only [*, left_distrib]
  right_distrib x y z := hf <| by simp only [*, right_distrib]
#align function.injective.distrib Function.Injective.distrib

def hasDistribNeg [Mul α] [HasDistribNeg α] (neg : ∀ a, f (-a) = -f a)
    (mul : ∀ a b, f (a * b) = f a * f b) : HasDistribNeg β :=
  { hf.involutiveNeg _ neg, ‹Mul β› with
    neg_mul := fun x y => hf <| by erw [neg, mul, neg, neg_mul, mul],
    mul_neg := fun x y => hf <| by erw [neg, mul, neg, mul_neg, mul] }
#align function.injective.has_distrib_neg Function.Injective.hasDistribNeg

def nonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring α] (zero : f 0 = 0)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) : NonUnitalNonAssocSemiring β where
  toAddCommMonoid := hf.addCommMonoid f zero add (swap nsmul)
  __ := hf.distrib f add mul
  __ := hf.mulZeroClass f zero mul
#align function.injective.non_unital_non_assoc_semiring Function.Injective.nonUnitalNonAssocSemiring

def nonUnitalSemiring [NonUnitalSemiring α]
    (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) :
    NonUnitalSemiring β where
  toNonUnitalNonAssocSemiring := hf.nonUnitalNonAssocSemiring f zero add mul nsmul
  __ := hf.semigroupWithZero f zero mul
#align function.injective.non_unital_semiring Function.Injective.nonUnitalSemiring

def nonAssocSemiring [NonAssocSemiring α]
    (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (nat_cast : ∀ n : ℕ, f n = n) : NonAssocSemiring β where
  toNonUnitalNonAssocSemiring := hf.nonUnitalNonAssocSemiring f zero add mul nsmul
  __ := hf.mulZeroOneClass f zero one mul
  __ := hf.addMonoidWithOne f zero one add nsmul nat_cast
#align function.injective.non_assoc_semiring Function.Injective.nonAssocSemiring

def semiring [Semiring α] (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (nat_cast : ∀ n : ℕ, f n = n) : Semiring β where
  toNonUnitalSemiring := hf.nonUnitalSemiring f zero add mul nsmul
  __ := hf.nonAssocSemiring f zero one add mul nsmul nat_cast
  __ := hf.monoidWithZero f zero one mul npow
#align function.injective.semiring Function.Injective.semiring

def nonUnitalNonAssocRing [NonUnitalNonAssocRing α] (f : β → α)
    (hf : Injective f) (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x) : NonUnitalNonAssocRing β where
  toAddCommGroup := hf.addCommGroup f zero add neg sub (swap nsmul) (swap zsmul)
  __ := hf.nonUnitalNonAssocSemiring f zero add mul nsmul
#align function.injective.non_unital_non_assoc_ring Function.Injective.nonUnitalNonAssocRing

def nonUnitalRing [NonUnitalRing α]
    (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x) :
    NonUnitalRing β where
  toNonUnitalNonAssocRing := hf.nonUnitalNonAssocRing f zero add mul neg sub nsmul zsmul
  __ := hf.nonUnitalSemiring f zero add mul nsmul
#align function.injective.non_unital_ring Function.Injective.nonUnitalRing

def nonAssocRing [NonAssocRing α]
    (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x) (nat_cast : ∀ n : ℕ, f n = n)
    (int_cast : ∀ n : ℤ, f n = n) : NonAssocRing β where
  toNonUnitalNonAssocRing := hf.nonUnitalNonAssocRing f zero add mul neg sub nsmul zsmul
  __ := hf.nonAssocSemiring f zero one add mul nsmul nat_cast
  __ := hf.addCommGroupWithOne f zero one add neg sub nsmul zsmul nat_cast int_cast
#align function.injective.non_assoc_ring Function.Injective.nonAssocRing

def ring [Ring α] (zero : f 0 = 0)
    (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (nat_cast : ∀ n : ℕ, f n = n)
    (int_cast : ∀ n : ℤ, f n = n) : Ring β where
  toSemiring := hf.semiring f zero one add mul nsmul npow nat_cast
  __ := hf.addGroupWithOne f zero one add neg sub nsmul zsmul nat_cast int_cast
  __ := hf.addCommGroup f zero add neg sub (swap nsmul) (swap zsmul)
#align function.injective.ring Function.Injective.ring

def nonUnitalNonAssocCommSemiring [NonUnitalNonAssocCommSemiring α]
    (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) :
    NonUnitalNonAssocCommSemiring β where
  toNonUnitalNonAssocSemiring := hf.nonUnitalNonAssocSemiring f zero add mul nsmul
  __ := hf.commMagma f mul

/-- Pullback a `NonUnitalCommSemiring` instance along an injective function. -/
@[reducible] -- See note [reducible non-instances]
protected def nonUnitalCommSemiring [NonUnitalCommSemiring α] (f : β → α)
    (hf : Injective f) (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) :
    NonUnitalCommSemiring β where
  toNonUnitalSemiring := hf.nonUnitalSemiring f zero add mul nsmul
  __ := hf.commSemigroup f mul
#align function.injective.non_unital_comm_semiring Function.Injective.nonUnitalCommSemiring

def commSemiring [CommSemiring α]
    (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (nat_cast : ∀ n : ℕ, f n = n) :
    CommSemiring β where
  toSemiring := hf.semiring f zero one add mul nsmul npow nat_cast
  __ := hf.commSemigroup f mul
#align function.injective.comm_semiring Function.Injective.commSemiring

def nonUnitalNonAssocCommRing [NonUnitalNonAssocCommRing α] (f : β → α)
    (hf : Injective f) (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x) : NonUnitalNonAssocCommRing β where
  toNonUnitalNonAssocRing := hf.nonUnitalNonAssocRing f zero add mul neg sub nsmul zsmul
  __ := hf.nonUnitalNonAssocCommSemiring f zero add mul nsmul

/-- Pullback a `NonUnitalCommRing` instance along an injective function. -/
@[reducible] -- -- See note [reducible non-instances]
protected def nonUnitalCommRing [NonUnitalCommRing α] (f : β → α)
    (hf : Injective f) (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x) : NonUnitalCommRing β where
  toNonUnitalRing := hf.nonUnitalRing f zero add mul neg sub nsmul zsmul
  __ := hf.nonUnitalNonAssocCommRing f zero add mul neg sub nsmul zsmul
#align function.injective.non_unital_comm_ring Function.Injective.nonUnitalCommRing

def commRing [CommRing α]
    (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (nat_cast : ∀ n : ℕ, f n = n) (int_cast : ∀ n : ℤ, f n = n) : CommRing β where
  toRing := hf.ring f zero one add mul neg sub nsmul zsmul npow nat_cast int_cast
  __ := hf.commMonoid f one mul npow
#align function.injective.comm_ring Function.Injective.commRing

def distrib [Distrib α] (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) : Distrib β where
  left_distrib := hf.forall₃.2 fun x y z => by simp only [← add, ← mul, left_distrib]
  right_distrib := hf.forall₃.2 fun x y z => by simp only [← add, ← mul, right_distrib]
#align function.surjective.distrib Function.Surjective.distrib

def hasDistribNeg [Mul α] [HasDistribNeg α]
    (neg : ∀ a, f (-a) = -f a) (mul : ∀ a b, f (a * b) = f a * f b) : HasDistribNeg β :=
  { hf.involutiveNeg _ neg, ‹Mul β› with
    neg_mul := hf.forall₂.2 fun x y => by erw [← neg, ← mul, neg_mul, neg, mul]
    mul_neg := hf.forall₂.2 fun x y => by erw [← neg, ← mul, mul_neg, neg, mul] }
#align function.surjective.has_distrib_neg Function.Surjective.hasDistribNeg

def nonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring α] (zero : f 0 = 0)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) : NonUnitalNonAssocSemiring β where
  toAddCommMonoid := hf.addCommMonoid f zero add (swap nsmul)
  __ := hf.distrib f add mul
  __ := hf.mulZeroClass f zero mul
#align function.surjective.non_unital_non_assoc_semiring Function.Surjective.nonUnitalNonAssocSemiring

def nonUnitalSemiring [NonUnitalSemiring α] (zero : f 0 = 0)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) : NonUnitalSemiring β where
  toNonUnitalNonAssocSemiring := hf.nonUnitalNonAssocSemiring f zero add mul nsmul
  __ := hf.semigroupWithZero f zero mul
#align function.surjective.non_unital_semiring Function.Surjective.nonUnitalSemiring

def nonAssocSemiring [NonAssocSemiring α] (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (nat_cast : ∀ n : ℕ, f n = n) : NonAssocSemiring β where
  toNonUnitalNonAssocSemiring := hf.nonUnitalNonAssocSemiring f zero add mul nsmul
  __ := hf.mulZeroOneClass f zero one mul
  __ := hf.addMonoidWithOne f zero one add nsmul nat_cast
#align function.surjective.non_assoc_semiring Function.Surjective.nonAssocSemiring

def semiring [Semiring α] (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (nat_cast : ∀ n : ℕ, f n = n) : Semiring β where
  toNonUnitalSemiring := hf.nonUnitalSemiring f zero add mul nsmul
  __ := hf.nonAssocSemiring f zero one add mul nsmul nat_cast
  __ := hf.monoidWithZero f zero one mul npow
#align function.surjective.semiring Function.Surjective.semiring

def nonUnitalNonAssocRing [NonUnitalNonAssocRing α] (zero : f 0 = 0)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x) :
    NonUnitalNonAssocRing β where
  toAddCommGroup := hf.addCommGroup f zero add neg sub (swap nsmul) (swap zsmul)
  __ := hf.nonUnitalNonAssocSemiring f zero add mul nsmul
#align function.surjective.non_unital_non_assoc_ring Function.Surjective.nonUnitalNonAssocRing

def nonUnitalRing [NonUnitalRing α] (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y)
    (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x) :
    NonUnitalRing β where
  toNonUnitalNonAssocRing := hf.nonUnitalNonAssocRing f zero add mul neg sub nsmul zsmul
  __ := hf.nonUnitalSemiring f zero add mul nsmul
#align function.surjective.non_unital_ring Function.Surjective.nonUnitalRing

def nonAssocRing [NonAssocRing α] (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x)
    (nat_cast : ∀ n : ℕ, f n = n) (int_cast : ∀ n : ℤ, f n = n) : NonAssocRing β where
  toNonUnitalNonAssocRing := hf.nonUnitalNonAssocRing f zero add mul neg sub nsmul zsmul
  __ := hf.nonAssocSemiring f zero one add mul nsmul nat_cast
  __ := hf.addCommGroupWithOne f zero one add neg sub nsmul zsmul nat_cast int_cast
#align function.surjective.non_assoc_ring Function.Surjective.nonAssocRing

def ring [Ring α] (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y)
    (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (nat_cast : ∀ n : ℕ, f n = n)
    (int_cast : ∀ n : ℤ, f n = n) : Ring β where
  toSemiring := hf.semiring f zero one add mul nsmul npow nat_cast
  __ := hf.addGroupWithOne f zero one add neg sub nsmul zsmul nat_cast int_cast
  __ := hf.addCommGroup f zero add neg sub (swap nsmul) (swap zsmul)
#align function.surjective.ring Function.Surjective.ring

def nonUnitalNonAssocCommSemiring  [NonUnitalNonAssocCommSemiring α] (zero : f 0 = 0)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) : NonUnitalNonAssocCommSemiring β where
  toNonUnitalNonAssocSemiring := hf.nonUnitalNonAssocSemiring f zero add mul nsmul
  __ := hf.commMagma f mul

/-- Pushforward a `NonUnitalCommSemiring` instance along a surjective function. -/
@[reducible] -- See note [reducible non-instances]
protected def nonUnitalCommSemiring [NonUnitalCommSemiring α] (zero : f 0 = 0)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) : NonUnitalCommSemiring β where
  toNonUnitalSemiring := hf.nonUnitalSemiring f zero add mul nsmul
  __ := hf.commSemigroup f mul
#align function.surjective.non_unital_comm_semiring Function.Surjective.nonUnitalCommSemiring

def commSemiring [CommSemiring α] (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (nat_cast : ∀ n : ℕ, f n = n) : CommSemiring β where
  toSemiring := hf.semiring f zero one add mul nsmul npow nat_cast
  __ := hf.commSemigroup f mul
#align function.surjective.comm_semiring Function.Surjective.commSemiring

def nonUnitalNonAssocCommRing [NonUnitalNonAssocCommRing α]
    (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x) : NonUnitalNonAssocCommRing β where
  toNonUnitalNonAssocRing := hf.nonUnitalNonAssocRing f zero add mul neg sub nsmul zsmul
  __ := hf.nonUnitalNonAssocCommSemiring f zero add mul nsmul

/-- Pushforward a `NonUnitalCommRing` instance along a surjective function. -/
@[reducible] -- See note [reducible non-instances]
protected def nonUnitalCommRing [NonUnitalCommRing α] (zero : f 0 = 0)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x) :
    NonUnitalCommRing β where
  toNonUnitalRing := hf.nonUnitalRing f zero add mul neg sub nsmul zsmul
  __ := hf.nonUnitalNonAssocCommRing f zero add mul neg sub nsmul zsmul
#align function.surjective.non_unital_comm_ring Function.Surjective.nonUnitalCommRing

def commRing [CommRing α] (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (nat_cast : ∀ n : ℕ, f n = n) (int_cast : ∀ n : ℤ, f n = n) : CommRing β where
  toRing := hf.ring f zero one add mul neg sub nsmul zsmul npow nat_cast int_cast
  __ := hf.commMonoid f one mul npow
#align function.surjective.comm_ring Function.Surjective.commRing