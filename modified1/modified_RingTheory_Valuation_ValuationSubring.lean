def ValueGroup :=
  ValuationRing.ValueGroup A K
-- deriving LinearOrderedCommGroupWithZero
#align valuation_subring.value_group ValuationSubring.ValueGroup

def valuation : Valuation K A.ValueGroup :=
  ValuationRing.valuation A K
#align valuation_subring.valuation ValuationSubring.valuation

def ofSubring (R : Subring K) (hR : ∀ x : K, x ∈ R ∨ x⁻¹ ∈ R) : ValuationSubring K :=
  { R with mem_or_inv_mem' := hR }
#align valuation_subring.of_subring ValuationSubring.ofSubring

def ofLE (R : ValuationSubring K) (S : Subring K) (h : R.toSubring ≤ S) : ValuationSubring K :=
  { S with mem_or_inv_mem' := fun x => (R.mem_or_inv_mem x).imp (@h x) (@h _) }
#align valuation_subring.of_le ValuationSubring.ofLE

def inclusion (R S : ValuationSubring K) (h : R ≤ S) : R →+* S :=
  Subring.inclusion h
#align valuation_subring.inclusion ValuationSubring.inclusion

def subtype (R : ValuationSubring K) : R →+* K :=
  Subring.subtype R.toSubring
#align valuation_subring.subtype ValuationSubring.subtype

def mapOfLE (R S : ValuationSubring K) (h : R ≤ S) : R.ValueGroup →*₀ S.ValueGroup where
  toFun := Quotient.map' id fun x y ⟨u, hu⟩ => ⟨Units.map (R.inclusion S h).toMonoidHom u, hu⟩
  map_zero' := rfl
  map_one' := rfl
  map_mul' := by rintro ⟨⟩ ⟨⟩; rfl
#align valuation_subring.map_of_le ValuationSubring.mapOfLE

def idealOfLE (R S : ValuationSubring K) (h : R ≤ S) : Ideal R :=
  (LocalRing.maximalIdeal S).comap (R.inclusion S h)
#align valuation_subring.ideal_of_le ValuationSubring.idealOfLE

def ofPrime (A : ValuationSubring K) (P : Ideal A) [P.IsPrime] : ValuationSubring K :=
  ofLE A (Localization.subalgebra.ofField K _ P.primeCompl_le_nonZeroDivisors).toSubring
    -- Porting note: added `Subalgebra.mem_toSubring.mpr`
    fun a ha => Subalgebra.mem_toSubring.mpr <|
      Subalgebra.algebraMap_mem
        (Localization.subalgebra.ofField K _ P.primeCompl_le_nonZeroDivisors) (⟨a, ha⟩ : A)
#align valuation_subring.of_prime ValuationSubring.ofPrime

def primeSpectrumEquiv : PrimeSpectrum A ≃ {S // A ≤ S} where
  toFun P := ⟨ofPrime A P.asIdeal, le_ofPrime _ _⟩
  invFun S := ⟨idealOfLE _ S S.2, inferInstance⟩
  left_inv P := by ext1; simp
  right_inv S := by ext1; simp
#align valuation_subring.prime_spectrum_equiv ValuationSubring.primeSpectrumEquiv

def primeSpectrumOrderEquiv : (PrimeSpectrum A)ᵒᵈ ≃o {S // A ≤ S} :=
  { primeSpectrumEquiv A with
    map_rel_iff' :=
      ⟨fun h => by
        dsimp at h
        have := idealOfLE_le_of_le A _ _ ?_ ?_ h
        iterate 2 erw [idealOfLE_ofPrime] at this
        exact this
        all_goals exact le_ofPrime A (PrimeSpectrum.asIdeal _),
      fun h => by apply ofPrime_le_of_le; exact h⟩ }
#align valuation_subring.prime_spectrum_order_equiv ValuationSubring.primeSpectrumOrderEquiv

def valuationSubring : ValuationSubring K :=
  { v.integer with
    mem_or_inv_mem' := by
      intro x
      rcases le_or_lt (v x) 1 with h | h
      · left; exact h
      · right; change v x⁻¹ ≤ 1
        rw [map_inv₀ v, ← inv_one, inv_le_inv₀]
        · exact le_of_lt h
        · intro c; simp [c] at h
        · exact one_ne_zero }
#align valuation.valuation_subring Valuation.valuationSubring

def unitGroup : Subgroup Kˣ :=
  (A.valuation.toMonoidWithZeroHom.toMonoidHom.comp (Units.coeHom K)).ker
#align valuation_subring.unit_group ValuationSubring.unitGroup

def unitGroupMulEquiv : A.unitGroup ≃* Aˣ where
  toFun x :=
    { val := ⟨(x : Kˣ), mem_of_valuation_le_one A _ x.prop.le⟩
      inv := ⟨((x⁻¹ : A.unitGroup) : Kˣ), mem_of_valuation_le_one _ _ x⁻¹.prop.le⟩
      -- Porting note: was `Units.mul_inv x`
      val_inv := Subtype.ext (by simp)
      -- Porting note: was `Units.inv_mul x`
      inv_val := Subtype.ext (by simp) }
  invFun x := ⟨Units.map A.subtype.toMonoidHom x, A.valuation_unit x⟩
  left_inv a := by ext; rfl
  right_inv a := by ext; rfl
  map_mul' a b := by ext; rfl
#align valuation_subring.unit_group_mul_equiv ValuationSubring.unitGroupMulEquiv

def unitGroupOrderEmbedding : ValuationSubring K ↪o Subgroup Kˣ where
  toFun A := A.unitGroup
  inj' := unitGroup_injective
  map_rel_iff' {_A _B} := unitGroup_le_unitGroup
#align valuation_subring.unit_group_order_embedding ValuationSubring.unitGroupOrderEmbedding

def nonunits : Subsemigroup K where
  carrier := {x | A.valuation x < 1}
  -- Porting note: added `Set.mem_setOf.mp`
  mul_mem' ha hb := (mul_lt_mul₀ (Set.mem_setOf.mp ha) (Set.mem_setOf.mp hb)).trans_eq <| mul_one _
#align valuation_subring.nonunits ValuationSubring.nonunits

def nonunitsOrderEmbedding : ValuationSubring K ↪o (Subsemigroup K)ᵒᵈ where
  toFun A := A.nonunits
  inj' := nonunits_injective
  map_rel_iff' {_A _B} := nonunits_le_nonunits
#align valuation_subring.nonunits_order_embedding ValuationSubring.nonunitsOrderEmbedding

def principalUnitGroup : Subgroup Kˣ where
  carrier := {x | A.valuation (x - 1) < 1}
  mul_mem' := by
    intro a b ha hb
    -- Porting note: added
    rw [Set.mem_setOf] at ha hb
    refine' lt_of_le_of_lt _ (max_lt hb ha)
    -- Porting note: `sub_add_sub_cancel` needed some help
    rw [← one_mul (A.valuation (b - 1)), ← A.valuation.map_one_add_of_lt ha, add_sub_cancel,
      ← Valuation.map_mul, mul_sub_one, ← sub_add_sub_cancel (↑(a * b) : K) _ 1]
    exact A.valuation.map_add _ _
  one_mem' := by simp
  inv_mem' := by
    dsimp
    intro a ha
    conv =>
      lhs
      rw [← mul_one (A.valuation _), ← A.valuation.map_one_add_of_lt ha]
    rwa [add_sub_cancel, ← Valuation.map_mul, sub_mul, Units.inv_mul, ← neg_sub, one_mul,
      Valuation.map_neg]
#align valuation_subring.principal_unit_group ValuationSubring.principalUnitGroup

def principalUnitGroupOrderEmbedding : ValuationSubring K ↪o (Subgroup Kˣ)ᵒᵈ where
  toFun A := A.principalUnitGroup
  inj' := principalUnitGroup_injective
  map_rel_iff' {_A _B} := principalUnitGroup_le_principalUnitGroup
#align valuation_subring.principal_unit_group_order_embedding ValuationSubring.principalUnitGroupOrderEmbedding

def principalUnitGroupEquiv :
    A.principalUnitGroup ≃* (Units.map (LocalRing.residue A).toMonoidHom).ker where
  toFun x :=
    ⟨A.unitGroupMulEquiv ⟨_, A.principal_units_le_units x.2⟩,
      A.coe_mem_principalUnitGroup_iff.1 x.2⟩
  invFun x :=
    ⟨A.unitGroupMulEquiv.symm x, by
      rw [A.coe_mem_principalUnitGroup_iff]; simpa using SetLike.coe_mem x⟩
  left_inv x := by simp
  right_inv x := by simp
  map_mul' x y := rfl
#align valuation_subring.principal_unit_group_equiv ValuationSubring.principalUnitGroupEquiv

def unitGroupToResidueFieldUnits : A.unitGroup →* (LocalRing.ResidueField A)ˣ :=
  MonoidHom.comp (Units.map <| (Ideal.Quotient.mk _).toMonoidHom) A.unitGroupMulEquiv.toMonoidHom
#align valuation_subring.unit_group_to_residue_field_units ValuationSubring.unitGroupToResidueFieldUnits

def unitsModPrincipalUnitsEquivResidueFieldUnits :
    A.unitGroup ⧸ A.principalUnitGroup.comap A.unitGroup.subtype ≃* (LocalRing.ResidueField A)ˣ :=
  (QuotientGroup.quotientMulEquivOfEq A.ker_unitGroupToResidueFieldUnits.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ A.surjective_unitGroupToResidueFieldUnits)
#align valuation_subring.units_mod_principal_units_equiv_residue_field_units ValuationSubring.unitsModPrincipalUnitsEquivResidueFieldUnits

def pointwiseHasSMul : SMul G (ValuationSubring K) where
  smul g S :=-- TODO: if we add `ValuationSubring.map` at a later date, we should use it here
    { g • S.toSubring with
      mem_or_inv_mem' := fun x =>
        (mem_or_inv_mem S (g⁻¹ • x)).imp Subring.mem_pointwise_smul_iff_inv_smul_mem.mpr fun h =>
          Subring.mem_pointwise_smul_iff_inv_smul_mem.mpr <| by rwa [smul_inv''] }
#align valuation_subring.pointwise_has_smul ValuationSubring.pointwiseHasSMul

def pointwiseMulAction : MulAction G (ValuationSubring K) :=
  toSubring_injective.mulAction toSubring pointwise_smul_toSubring
#align valuation_subring.pointwise_mul_action ValuationSubring.pointwiseMulAction

def comap (A : ValuationSubring L) (f : K →+* L) : ValuationSubring K :=
  { A.toSubring.comap f with mem_or_inv_mem' := fun k => by simp [ValuationSubring.mem_or_inv_mem] }
#align valuation_subring.comap ValuationSubring.comap

structure on `ValuationSubring K`.

-/


universe u

open scoped Classical

noncomputable section

variable (K : Type u) [Field K]

/-- A valuation subring of a field `K` is a subring `A` such that for every `x : K`,
either `x ∈ A` or `x⁻¹ ∈ A`. -/
structure ValuationSubring extends Subring K where
  mem_or_inv_mem' : ∀ x : K, x ∈ carrier ∨ x⁻¹ ∈ carrier
#align valuation_subring ValuationSubring