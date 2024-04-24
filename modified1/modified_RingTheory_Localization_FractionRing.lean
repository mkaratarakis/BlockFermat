def inv (z : K) : K := open scoped Classical in
  if h : z = 0 then 0
  else
    mk' K ↑(sec (nonZeroDivisors A) z).2
      ⟨(sec _ z).1,
        mem_nonZeroDivisors_iff_ne_zero.2 fun h0 =>
          h <| eq_zero_of_fst_eq_zero (sec_spec (nonZeroDivisors A) z) h0⟩
#align is_fraction_ring.inv IsFractionRing.inv

def toField : Field K :=
  { IsFractionRing.isDomain A, inferInstanceAs (CommRing K) with
    inv := IsFractionRing.inv A
    mul_inv_cancel := IsFractionRing.mul_inv_cancel A
    inv_zero := by
      change IsFractionRing.inv A (0 : K) = 0
      rw [IsFractionRing.inv]
      exact dif_pos rfl
    qsmul := qsmulRec _ }
#align is_fraction_ring.to_field IsFractionRing.toField

def lift (hg : Injective g) : K →+* L :=
  IsLocalization.lift fun y : nonZeroDivisors A => isUnit_map_of_injective hg y
#align is_fraction_ring.lift IsFractionRing.lift

def map {A B K L : Type*} [CommRing A] [CommRing B] [IsDomain B] [CommRing K]
    [Algebra A K] [IsFractionRing A K] [CommRing L] [Algebra B L] [IsFractionRing B L] {j : A →+* B}
    (hj : Injective j) : K →+* L :=
  IsLocalization.map L j
    (show nonZeroDivisors A ≤ (nonZeroDivisors B).comap j from
      nonZeroDivisors_le_comap_nonZeroDivisors_of_injective j hj)
#align is_fraction_ring.map IsFractionRing.map

def fieldEquivOfRingEquiv [Algebra B L] [IsFractionRing B L] (h : A ≃+* B) :
    K ≃+* L :=
  ringEquivOfRingEquiv K L h
    (by
      ext b
      show b ∈ h.toEquiv '' _ ↔ _
      erw [h.toEquiv.image_eq_preimage, Set.preimage, Set.mem_setOf_eq,
        mem_nonZeroDivisors_iff_ne_zero, mem_nonZeroDivisors_iff_ne_zero]
      exact h.symm.map_ne_zero_iff)
#align is_fraction_ring.field_equiv_of_ring_equiv IsFractionRing.fieldEquivOfRingEquiv

def FractionRing :=
  Localization (nonZeroDivisors R)
#align fraction_ring FractionRing

def liftAlgebra [IsDomain R] [Field K] [Algebra R K]
    [NoZeroSMulDivisors R K] : Algebra (FractionRing R) K :=
  RingHom.toAlgebra (IsFractionRing.lift (NoZeroSMulDivisors.algebraMap_injective R _))

-- Porting note: had to fill in the `_` by hand for this instance
instance isScalarTower_liftAlgebra [IsDomain R] [Field K] [Algebra R K] [NoZeroSMulDivisors R K] :
    by letI := liftAlgebra R K; exact IsScalarTower R (FractionRing R) K := by
  letI := liftAlgebra R K
  exact IsScalarTower.of_algebraMap_eq fun x =>
    (IsFractionRing.lift_algebraMap (NoZeroSMulDivisors.algebraMap_injective R K) x).symm

/-- Given an integral domain `A` and a localization map to a field of fractions
`f : A →+* K`, we get an `A`-isomorphism between the field of fractions of `A` as a quotient
type and `K`. -/
noncomputable def algEquiv (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K] :
    FractionRing A ≃ₐ[A] K :=
  Localization.algEquiv (nonZeroDivisors A) K
#align fraction_ring.alg_equiv FractionRing.algEquiv