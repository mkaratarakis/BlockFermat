def lift_aux : L →ₐ[K] M :=
  Classical.choice <| IntermediateField.nonempty_algHom_of_adjoin_splits
    (fun x _ ↦ ⟨(hL x).isIntegral, splits_codomain (minpoly K x)⟩)
    (IntermediateField.adjoin_univ K L)

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [IsDomain S] [Algebra R S] [Algebra R M] [NoZeroSMulDivisors R S]
  [NoZeroSMulDivisors R M] (hS : Algebra.IsAlgebraic R S)

variable {M}

private theorem FractionRing.isAlgebraic :
    letI : IsDomain R := (NoZeroSMulDivisors.algebraMap_injective R S).isDomain _
    letI : Algebra (FractionRing R) (FractionRing S) := FractionRing.liftAlgebra R _
    Algebra.IsAlgebraic (FractionRing R) (FractionRing S) := by
  letI : IsDomain R := (NoZeroSMulDivisors.algebraMap_injective R S).isDomain _
  letI : Algebra (FractionRing R) (FractionRing S) := FractionRing.liftAlgebra R _
  have := FractionRing.isScalarTower_liftAlgebra R (FractionRing S)
  intro
  exact
    (IsFractionRing.isAlgebraic_iff R (FractionRing R) (FractionRing S)).1
      ((IsFractionRing.isAlgebraic_iff' R S (FractionRing S)).1 hS _)

/-- A (random) homomorphism from an algebraic extension of R into an algebraically
  closed extension of R. -/
noncomputable irreducible_def lift : S →ₐ[R] M := by
  letI : IsDomain R := (NoZeroSMulDivisors.algebraMap_injective R S).isDomain _
  letI := FractionRing.liftAlgebra R M
  letI := FractionRing.liftAlgebra R (FractionRing S)
  have := FractionRing.isScalarTower_liftAlgebra R M
  have := FractionRing.isScalarTower_liftAlgebra R (FractionRing S)
  have : Algebra.IsAlgebraic (FractionRing R) (FractionRing S) :=
    FractionRing.isAlgebraic hS
  let f : FractionRing S →ₐ[FractionRing R] M := lift_aux (FractionRing R) (FractionRing S) M this
  exact (f.restrictScalars R).comp ((Algebra.ofId S (FractionRing S)).restrictScalars R)
#align is_alg_closed.lift IsAlgClosed.lift

def equiv : L ≃ₐ[R] M :=
  -- Porting note (#10754): added to replace local instance above

def equivOfAlgebraic' [Nontrivial S] [NoZeroSMulDivisors R S]
    (hRL : Algebra.IsAlgebraic R L) : L ≃ₐ[R] M := by
  letI : NoZeroSMulDivisors R L := NoZeroSMulDivisors.of_algebraMap_injective <| by
    rw [IsScalarTower.algebraMap_eq R S L]
    exact (Function.Injective.comp (NoZeroSMulDivisors.algebraMap_injective S L)
            (NoZeroSMulDivisors.algebraMap_injective R S) : _)
  letI : IsAlgClosure R L :=
    { alg_closed := IsAlgClosure.alg_closed S
      algebraic := hRL }
  exact IsAlgClosure.equiv _ _ _
#align is_alg_closure.equiv_of_algebraic' IsAlgClosure.equivOfAlgebraic'

def equivOfAlgebraic (hKJ : Algebra.IsAlgebraic K J) : L ≃ₐ[K] M :=
  equivOfAlgebraic' K J _ _ (hKJ.trans IsAlgClosure.algebraic)
#align is_alg_closure.equiv_of_algebraic IsAlgClosure.equivOfAlgebraic

def equivOfEquivAux (hSR : S ≃+* R) :
    { e : L ≃+* M // e.toRingHom.comp (algebraMap S L) = (algebraMap R M).comp hSR.toRingHom } := by
  letI : Algebra R S := RingHom.toAlgebra hSR.symm.toRingHom
  letI : Algebra S R := RingHom.toAlgebra hSR.toRingHom
  letI : IsDomain R := (NoZeroSMulDivisors.algebraMap_injective R M).isDomain _
  letI : IsDomain S := (NoZeroSMulDivisors.algebraMap_injective S L).isDomain _
  letI : Algebra R L := RingHom.toAlgebra ((algebraMap S L).comp (algebraMap R S))
  haveI : IsScalarTower R S L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower S R L :=
    IsScalarTower.of_algebraMap_eq (by simp [RingHom.algebraMap_toAlgebra])
  haveI : NoZeroSMulDivisors R S := NoZeroSMulDivisors.of_algebraMap_injective hSR.symm.injective
  refine
    ⟨equivOfAlgebraic' R S L M
        (IsAlgClosure.algebraic.tower_top_of_injective
          (show Function.Injective (algebraMap S R) from hSR.injective)), ?_⟩
  ext x
  simp only [RingEquiv.toRingHom_eq_coe, Function.comp_apply, RingHom.coe_comp,
    AlgEquiv.coe_ringEquiv, RingEquiv.coe_toRingHom]
  conv_lhs => rw [← hSR.symm_apply_apply x]
  show equivOfAlgebraic' R S L M _ (algebraMap R L (hSR x)) = _
  rw [AlgEquiv.commutes]
#align is_alg_closure.equiv_of_equiv_aux IsAlgClosure.equivOfEquivAux

def equivOfEquiv (hSR : S ≃+* R) : L ≃+* M :=
  equivOfEquivAux L M hSR
#align is_alg_closure.equiv_of_equiv IsAlgClosure.equivOfEquiv