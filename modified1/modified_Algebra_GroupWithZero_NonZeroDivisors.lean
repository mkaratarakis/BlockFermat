def nonZeroDivisorsLeft : Submonoid M₀ where
  carrier := {x | ∀ y, y * x = 0 → y = 0}
  one_mem' := by simp
  mul_mem' {x} {y} hx hy := fun z hz ↦ hx _ <| hy _ (mul_assoc z x y ▸ hz)

@[simp] lemma mem_nonZeroDivisorsLeft_iff {x : M₀} :
    x ∈ nonZeroDivisorsLeft M₀ ↔ ∀ y, y * x = 0 → y = 0 :=
  Iff.rfl

/-- The collection of elements of a `MonoidWithZero` that are not right zero divisors form a
`Submonoid`. -/
def nonZeroDivisorsRight : Submonoid M₀ where
  carrier := {x | ∀ y, x * y = 0 → y = 0}
  one_mem' := by simp
  mul_mem' := fun {x} {y} hx hy z hz ↦ hy _ (hx _ ((mul_assoc x y z).symm ▸ hz))

@[simp] lemma mem_nonZeroDivisorsRight_iff {x : M₀} :
    x ∈ nonZeroDivisorsRight M₀ ↔ ∀ y, x * y = 0 → y = 0 :=
  Iff.rfl

lemma nonZeroDivisorsLeft_eq_right (M₀ : Type*) [CommMonoidWithZero M₀] :
    nonZeroDivisorsLeft M₀ = nonZeroDivisorsRight M₀ := by
  ext x; simp [mul_comm x]

@[simp] lemma coe_nonZeroDivisorsLeft_eq [NoZeroDivisors M₀] [Nontrivial M₀] :
    nonZeroDivisorsLeft M₀ = {x : M₀ | x ≠ 0} := by
  ext x
  simp only [SetLike.mem_coe, mem_nonZeroDivisorsLeft_iff, mul_eq_zero, forall_eq_or_imp, true_and,
    Set.mem_setOf_eq]
  refine' ⟨fun h ↦ _, fun hx y hx' ↦ by contradiction⟩
  contrapose! h
  exact ⟨1, h, one_ne_zero⟩

@[simp] lemma coe_nonZeroDivisorsRight_eq [NoZeroDivisors M₀] [Nontrivial M₀] :
    nonZeroDivisorsRight M₀ = {x : M₀ | x ≠ 0} := by
  ext x
  simp only [SetLike.mem_coe, mem_nonZeroDivisorsRight_iff, mul_eq_zero, Set.mem_setOf_eq]
  refine' ⟨fun h ↦ _, fun hx y hx' ↦ by aesop⟩
  contrapose! h
  exact ⟨1, Or.inl h, one_ne_zero⟩

/-- The submonoid of non-zero-divisors of a `MonoidWithZero` `R`. -/
def nonZeroDivisors (R : Type*) [MonoidWithZero R] : Submonoid R where
  carrier := { x | ∀ z, z * x = 0 → z = 0 }
  one_mem' _ hz := by rwa [mul_one] at hz
  mul_mem' hx₁ hx₂ _ hz := by
    rw [← mul_assoc] at hz
    exact hx₁ _ (hx₂ _ hz)
#align non_zero_divisors nonZeroDivisors

def nonZeroSMulDivisors (R : Type*) [MonoidWithZero R] (M : Type _) [Zero M] [MulAction R M] :
    Submonoid R where
  carrier := { r | ∀ m : M, r • m = 0 → m = 0}
  one_mem' m h := (one_smul R m) ▸ h
  mul_mem' {r₁ r₂} h₁ h₂ m H := h₂ _ <| h₁ _ <| mul_smul r₁ r₂ m ▸ H

/-- The notation for the submonoid of non-zero smul-divisors. -/
scoped[nonZeroSMulDivisors] notation:9000 R "⁰[" M "]" => nonZeroSMulDivisors R M

section nonZeroDivisors

open nonZeroDivisors

variable {M M' M₁ R R' F : Type*} [MonoidWithZero M] [MonoidWithZero M'] [CommMonoidWithZero M₁]
  [Ring R] [CommRing R']

theorem mem_nonZeroDivisors_iff {r : M} : r ∈ M⁰ ↔ ∀ x, x * r = 0 → x = 0 := Iff.rfl
#align mem_non_zero_divisors_iff mem_nonZeroDivisors_iff