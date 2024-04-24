def MulAut (M : Type*) [Mul M] :=
  M ≃* M
#align mul_aut MulAut

def (e₁ e₂ : MulAut M) : e₁ * e₂ = e₂.trans e₁ :=
  rfl
#align mul_aut.mul_def MulAut.mul_def

def : (1 : MulAut M) = MulEquiv.refl _ :=
  rfl
#align mul_aut.one_def MulAut.one_def

def (e₁ : MulAut M) : e₁⁻¹ = e₁.symm :=
  rfl
#align mul_aut.inv_def MulAut.inv_def

def toPerm : MulAut M →* Equiv.Perm M := by
  refine' { toFun := MulEquiv.toEquiv, ..} <;> intros <;> rfl
#align mul_aut.to_perm MulAut.toPerm

def {M} [Monoid M] (f : MulAut M) (a : M) : f • a = f a :=
  rfl
#align mul_aut.smul_def MulAut.smul_def

def conj [Group G] : G →* MulAut G where
  toFun g :=
    { toFun := fun h => g * h * g⁻¹
      invFun := fun h => g⁻¹ * h * g
      left_inv := fun _ => by simp only [mul_assoc, inv_mul_cancel_left, mul_left_inv, mul_one]
      right_inv := fun _ => by simp only [mul_assoc, mul_inv_cancel_left, mul_right_inv, mul_one]
      map_mul' := by simp only [mul_assoc, inv_mul_cancel_left, forall_const] }
  map_mul' g₁ g₂ := by
    ext h
    show g₁ * g₂ * h * (g₁ * g₂)⁻¹ = g₁ * (g₂ * h * g₂⁻¹) * g₁⁻¹
    simp only [mul_assoc, mul_inv_rev]
  map_one' := by ext; simp only [one_mul, inv_one, mul_one, one_apply]; rfl
#align mul_aut.conj MulAut.conj

def (e₁ e₂ : AddAut A) : e₁ * e₂ = e₂.trans e₁ :=
  rfl
#align add_aut.mul_def AddAut.mul_def

def : (1 : AddAut A) = AddEquiv.refl _ :=
  rfl
#align add_aut.one_def AddAut.one_def

def (e₁ : AddAut A) : e₁⁻¹ = e₁.symm :=
  rfl
#align add_aut.inv_def AddAut.inv_def

def toPerm : AddAut A →* Equiv.Perm A := by
  refine' { toFun := AddEquiv.toEquiv, .. } <;> intros <;> rfl
#align add_aut.to_perm AddAut.toPerm

def {A} [AddMonoid A] (f : AddAut A) (a : A) : f • a = f a :=
  rfl
#align add_aut.smul_def AddAut.smul_def

def conj [AddGroup G] : G →+ Additive (AddAut G) where
  toFun g :=
    @Additive.ofMul (AddAut G)
      { toFun := fun h => g + h + -g
        -- this definition is chosen to match `MulAut.conj`
        invFun := fun h => -g + h + g
        left_inv := fun _ => by simp only [add_assoc, neg_add_cancel_left, add_left_neg, add_zero]
        right_inv := fun _ => by simp only [add_assoc, add_neg_cancel_left, add_right_neg, add_zero]
        map_add' := by simp only [add_assoc, neg_add_cancel_left, forall_const] }
  map_add' g₁ g₂ := by
    apply Additive.toMul.injective; ext h
    show g₁ + g₂ + h + -(g₁ + g₂) = g₁ + (g₂ + h + -g₂) + -g₁
    simp only [add_assoc, neg_add_rev]
  map_zero' := by
    apply Additive.toMul.injective; ext
    simp only [zero_add, neg_zero, add_zero, toMul_ofMul, toMul_zero, one_apply]
    rfl
#align add_aut.conj AddAut.conj

structure on `AddAut R := AddEquiv R R` and
`MulAut R := MulEquiv R R`.

## Implementation notes

structure is defined.

## Tags