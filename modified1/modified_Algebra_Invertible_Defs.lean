def something_that_needs_inverses (x : α) [Invertible x] := sorry

section
attribute [local instance] invertibleOne
def something_one := something_that_needs_inverses 1
end
```

### Typeclass search vs. unification for `simp` lemmas

def Invertible.copy' [MulOneClass α] {r : α} (hr : Invertible r) (s : α) (si : α) (hs : s = r)
    (hsi : si = ⅟ r) : Invertible s where
  invOf := si
  invOf_mul_self := by rw [hs, hsi, invOf_mul_self]
  mul_invOf_self := by rw [hs, hsi, mul_invOf_self]
#align invertible.copy' Invertible.copy'

def Invertible.copy [MulOneClass α] {r : α} (hr : Invertible r) (s : α) (hs : s = r) :
    Invertible s :=
  hr.copy' _ _ hs rfl
#align invertible.copy Invertible.copy

def invertibleOfGroup [Group α] (a : α) : Invertible a :=
  ⟨a⁻¹, inv_mul_self a, mul_inv_self a⟩
#align invertible_of_group invertibleOfGroup

def invertibleOne [Monoid α] : Invertible (1 : α) :=
  ⟨1, mul_one _, one_mul _⟩
#align invertible_one invertibleOne

def invertibleMul [Monoid α] (a b : α) [Invertible a] [Invertible b] : Invertible (a * b) :=
  ⟨⅟ b * ⅟ a, by simp [← mul_assoc], by simp [← mul_assoc]⟩
#align invertible_mul invertibleMul

def Invertible.mul [Monoid α] {a b : α} (_ : Invertible a) (_ : Invertible b) :
    Invertible (a * b) :=
  invertibleMul _ _
#align invertible.mul Invertible.mul