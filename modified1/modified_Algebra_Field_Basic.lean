def DivisionRing.ofIsUnitOrEqZero [Ring R] (h : ∀ a : R, IsUnit a ∨ a = 0) :
    DivisionRing R where
  toRing := ‹Ring R›
  __ := groupWithZeroOfIsUnitOrEqZero h
  qsmul := _
#align division_ring_of_is_unit_or_eq_zero DivisionRing.ofIsUnitOrEqZero

def Field.ofIsUnitOrEqZero [CommRing R] (h : ∀ a : R, IsUnit a ∨ a = 0) :
    Field R where
  toCommRing := ‹CommRing R›
  __ := DivisionRing.ofIsUnitOrEqZero h
#align field_of_is_unit_or_eq_zero Field.ofIsUnitOrEqZero

def divisionSemiring [DivisionSemiring β] (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (inv : ∀ x, f x⁻¹ = (f x)⁻¹) (div : ∀ x y, f (x / y) = f x / f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n)
    (natCast : ∀ n : ℕ, f n = n) : DivisionSemiring α where
  toSemiring := hf.semiring f zero one add mul nsmul npow natCast
  __ := hf.groupWithZero f zero one mul inv div npow zpow
#align function.injective.division_semiring Function.Injective.divisionSemiring

def divisionRing [DivisionRing β] (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
    (div : ∀ x y, f (x / y) = f x / f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x) (qsmul : ∀ (q : ℚ) (x), f (q • x) = q • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n)
    (natCast : ∀ n : ℕ, f n = n) (intCast : ∀ n : ℤ, f n = n)
    (ratCast : ∀ q : ℚ, f q = q) : DivisionRing α where
  toRing := hf.ring f zero one add mul neg sub nsmul zsmul npow natCast intCast
  __ := hf.groupWithZero f zero one mul inv div npow zpow
  __ := hf.divisionSemiring f zero one add mul inv div nsmul npow zpow natCast
  ratCast_def q := hf $ by erw [ratCast, div, intCast, natCast, Rat.cast_def]
  qsmul := (· • ·)
  qsmul_def q a := hf $ by erw [qsmul, mul, Rat.smul_def, ratCast]
#align function.injective.division_ring Function.Injective.divisionRing

def semifield [Semifield β] (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (inv : ∀ x, f x⁻¹ = (f x)⁻¹) (div : ∀ x y, f (x / y) = f x / f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n)
    (natCast : ∀ n : ℕ, f n = n) : Semifield α where
  toCommSemiring := hf.commSemiring f zero one add mul nsmul npow natCast
  __ := hf.commGroupWithZero f zero one mul inv div npow zpow
  __ := hf.divisionSemiring f zero one add mul inv div nsmul npow zpow natCast
#align function.injective.semifield Function.Injective.semifield

def field [Field β] (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
    (div : ∀ x y, f (x / y) = f x / f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x) (qsmul : ∀ (q : ℚ) (x), f (q • x) = q • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n)
    (natCast : ∀ n : ℕ, f n = n) (intCast : ∀ n : ℤ, f n = n)
    (ratCast : ∀ q : ℚ, f q = q) :
    Field α where
  toCommRing := hf.commRing f zero one add mul neg sub nsmul zsmul npow natCast intCast
  __ := hf.divisionRing f zero one add mul neg sub inv div nsmul zsmul qsmul npow zpow
    natCast intCast ratCast
#align function.injective.field Function.Injective.field

structure on a `Ring` consisting only of units and 0. -/
@[reducible] -- See note [reducible non-instances]
noncomputable def DivisionRing.ofIsUnitOrEqZero [Ring R] (h : ∀ a : R, IsUnit a ∨ a = 0) :
    DivisionRing R where
  toRing := ‹Ring R›
  __ := groupWithZeroOfIsUnitOrEqZero h
  qsmul := _
#align division_ring_of_is_unit_or_eq_zero DivisionRing.ofIsUnitOrEqZero

structure on a `CommRing` consisting only of units and 0. -/
@[reducible] -- See note [reducible non-instances]
noncomputable def Field.ofIsUnitOrEqZero [CommRing R] (h : ∀ a : R, IsUnit a ∨ a = 0) :
    Field R where
  toCommRing := ‹CommRing R›
  __ := DivisionRing.ofIsUnitOrEqZero h
#align field_of_is_unit_or_eq_zero Field.ofIsUnitOrEqZero