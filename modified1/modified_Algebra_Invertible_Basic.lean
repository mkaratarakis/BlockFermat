def unitOfInvertible [Monoid α] (a : α) [Invertible a] : αˣ where
  val := a
  inv := ⅟ a
  val_inv := by simp
  inv_val := by simp
#align unit_of_invertible unitOfInvertible

def Units.invertible [Monoid α] (u : αˣ) :
    Invertible (u : α) where
  invOf := ↑u⁻¹
  invOf_mul_self := u.inv_mul
  mul_invOf_self := u.mul_inv
#align units.invertible Units.invertible

def IsUnit.invertible [Monoid α] {a : α} (h : IsUnit a) : Invertible a :=
  Classical.choice h.nonempty_invertible
#align is_unit.invertible IsUnit.invertible

def invertibleNeg [Mul α] [One α] [HasDistribNeg α] (a : α) [Invertible a] : Invertible (-a) :=
  ⟨-⅟ a, by simp, by simp⟩
#align invertible_neg invertibleNeg

def invertibleOfInvertibleMul (a b : α) [Invertible a] [Invertible (a * b)] : Invertible b where
  invOf := ⅟ (a * b) * a
  invOf_mul_self := by rw [mul_assoc, invOf_mul_self]
  mul_invOf_self := by
    rw [← (isUnit_of_invertible a).mul_right_inj, ← mul_assoc, ← mul_assoc, mul_invOf_self, mul_one,
      one_mul]
#align invertible_of_invertible_mul invertibleOfInvertibleMul

def invertibleOfMulInvertible (a b : α) [Invertible (a * b)] [Invertible b] : Invertible a where
  invOf := b * ⅟ (a * b)
  invOf_mul_self := by
    rw [← (isUnit_of_invertible b).mul_left_inj, mul_assoc, mul_assoc, invOf_mul_self, mul_one,
      one_mul]
  mul_invOf_self := by rw [← mul_assoc, mul_invOf_self]
#align invertible_of_mul_invertible invertibleOfMulInvertible

def Invertible.mulLeft {a : α} (_ : Invertible a) (b : α) : Invertible b ≃ Invertible (a * b) where
  toFun _ := invertibleMul a b
  invFun _ := invertibleOfInvertibleMul a _
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
#align invertible.mul_left Invertible.mulLeft

def Invertible.mulRight (a : α) {b : α} (_ : Invertible b) : Invertible a ≃ Invertible (a * b) where
  toFun _ := invertibleMul a b
  invFun _ := invertibleOfMulInvertible _ b
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
#align invertible.mul_right Invertible.mulRight

def invertibleOfPowEqOne (x : α) (n : ℕ) (hx : x ^ n = 1) (hn : n ≠ 0) : Invertible x :=
  (Units.ofPowEqOne x n hx hn).invertible
#align invertible_of_pow_eq_one invertibleOfPowEqOne

def invertibleDiv (a b : α) [Invertible a] [Invertible b] : Invertible (a / b) :=
  ⟨b / a, by simp [← mul_div_assoc], by simp [← mul_div_assoc]⟩
#align invertible_div invertibleDiv

def Invertible.map {R : Type*} {S : Type*} {F : Type*} [MulOneClass R] [MulOneClass S]
    [FunLike F R S] [MonoidHomClass F R S] (f : F) (r : R) [Invertible r] :
    Invertible (f r) where
  invOf := f (⅟ r)
  invOf_mul_self := by rw [← map_mul, invOf_mul_self, map_one]
  mul_invOf_self := by rw [← map_mul, mul_invOf_self, map_one]
#align invertible.map Invertible.map

def Invertible.ofLeftInverse {R : Type*} {S : Type*} {G : Type*} [MulOneClass R] [MulOneClass S]
    [FunLike G S R] [MonoidHomClass G S R] (f : R → S) (g : G) (r : R)
    (h : Function.LeftInverse g f) [Invertible (f r)] : Invertible r :=
  (Invertible.map g (f r)).copy _ (h r).symm
#align invertible.of_left_inverse Invertible.ofLeftInverse

def invertibleEquivOfLeftInverse {R : Type*} {S : Type*} {F G : Type*} [Monoid R] [Monoid S]
    [FunLike F R S] [MonoidHomClass F R S] [FunLike G S R] [MonoidHomClass G S R]
    (f : F) (g : G) (r : R) (h : Function.LeftInverse g f) :
    Invertible (f r) ≃
      Invertible r where
  toFun _ := Invertible.ofLeftInverse f _ _ h
  invFun _ := Invertible.map f _
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
#align invertible_equiv_of_left_inverse invertibleEquivOfLeftInverse