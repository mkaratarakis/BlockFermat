def ringOfIntegers :=
  integralClosure ℤ K
#align number_field.ring_of_integers NumberField.ringOfIntegers

def equiv (R : Type*) [CommRing R] [Algebra R K]
    [IsIntegralClosure R ℤ K] : 𝓞 K ≃+* R :=
  (IsIntegralClosure.equiv ℤ R K _).symm.toRingEquiv
#align number_field.ring_of_integers.equiv NumberField.RingOfIntegers.equiv

def basis : Basis (Free.ChooseBasisIndex ℤ (𝓞 K)) ℤ (𝓞 K) :=
  Free.chooseBasis ℤ (𝓞 K)
#align number_field.ring_of_integers.basis NumberField.RingOfIntegers.basis

def integralBasis : Basis (Free.ChooseBasisIndex ℤ (𝓞 K)) ℚ K :=
  Basis.localizationLocalization ℚ (nonZeroDivisors ℤ) K (RingOfIntegers.basis K)
#align number_field.integral_basis NumberField.integralBasis

def ringOfIntegersEquiv : ringOfIntegers ℚ ≃+* ℤ :=
  RingOfIntegers.equiv ℤ
#align rat.ring_of_integers_equiv Rat.ringOfIntegersEquiv

structure is not a field. -/
theorem Int.not_isField : ¬IsField ℤ := fun h =>
  Int.not_even_one <|
    (h.mul_inv_cancel two_ne_zero).imp fun a => by rw [← two_mul]; exact Eq.symm
#align int.not_is_field Int.not_isField

structure of `ℚ` over itself can arise in multiple ways:
  -- all fields are vector spaces over themselves (used in `Rat.finiteDimensional`)
  -- all char 0 fields have a canonical embedding of `ℚ` (used in `NumberField`).
  -- Show that these coincide:
    convert (inferInstance : FiniteDimensional ℚ ℚ)
#align rat.number_field Rat.numberField