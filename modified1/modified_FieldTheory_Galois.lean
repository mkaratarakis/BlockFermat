def FixedPoints.intermediateField (M : Type*) [Monoid M] [MulSemiringAction M E]
    [SMulCommClass M F E] : IntermediateField F E :=
  { FixedPoints.subfield M E with
    carrier := MulAction.fixedPoints M E
    algebraMap_mem' := fun a g => smul_algebraMap g a }
#align fixed_points.intermediate_field FixedPoints.intermediateField

def fixedField : IntermediateField F E :=
  FixedPoints.intermediateField H
#align intermediate_field.fixed_field IntermediateField.fixedField

def fixingSubgroup : Subgroup (E ≃ₐ[F] E) :=
  fixingSubgroup (E ≃ₐ[F] E) (K : Set E)
#align intermediate_field.fixing_subgroup IntermediateField.fixingSubgroup

def fixingSubgroupEquiv : fixingSubgroup K ≃* E ≃ₐ[K] E where
  toFun ϕ := { AlgEquiv.toRingEquiv (ϕ : E ≃ₐ[F] E) with commutes' := ϕ.mem }
  invFun ϕ := ⟨ϕ.restrictScalars _, ϕ.commutes⟩
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl
  map_mul' _ _ := by ext; rfl
#align intermediate_field.fixing_subgroup_equiv IntermediateField.fixingSubgroupEquiv

def intermediateFieldEquivSubgroup [FiniteDimensional F E] [IsGalois F E] :
    IntermediateField F E ≃o (Subgroup (E ≃ₐ[F] E))ᵒᵈ where
  toFun := IntermediateField.fixingSubgroup
  invFun := IntermediateField.fixedField
  left_inv K := fixedField_fixingSubgroup K
  right_inv H := IntermediateField.fixingSubgroup_fixedField H
  map_rel_iff' {K L} := by
    rw [← fixedField_fixingSubgroup L, IntermediateField.le_iff_le, fixedField_fixingSubgroup L]
    rfl
#align is_galois.intermediate_field_equiv_subgroup IsGalois.intermediateFieldEquivSubgroup

def galoisInsertionIntermediateFieldSubgroup [FiniteDimensional F E] :
    GaloisInsertion (OrderDual.toDual ∘
      (IntermediateField.fixingSubgroup : IntermediateField F E → Subgroup (E ≃ₐ[F] E)))
      ((IntermediateField.fixedField : Subgroup (E ≃ₐ[F] E) → IntermediateField F E) ∘
        OrderDual.toDual) where
  choice K _ := IntermediateField.fixingSubgroup K
  gc K H := (IntermediateField.le_iff_le H K).symm
  le_l_u H := le_of_eq (IntermediateField.fixingSubgroup_fixedField H).symm
  choice_eq _ _ := rfl
#align is_galois.galois_insertion_intermediate_field_subgroup IsGalois.galoisInsertionIntermediateFieldSubgroup

def galoisCoinsertionIntermediateFieldSubgroup [FiniteDimensional F E] [IsGalois F E] :
    GaloisCoinsertion (OrderDual.toDual ∘
      (IntermediateField.fixingSubgroup : IntermediateField F E → Subgroup (E ≃ₐ[F] E)))
      ((IntermediateField.fixedField : Subgroup (E ≃ₐ[F] E) → IntermediateField F E) ∘
        OrderDual.toDual) where
  choice H _ := IntermediateField.fixedField H
  gc K H := (IntermediateField.le_iff_le H K).symm
  u_l_le K := le_of_eq (fixedField_fixingSubgroup K)
  choice_eq _ _ := rfl
#align is_galois.galois_coinsertion_intermediate_field_subgroup IsGalois.galoisCoinsertionIntermediateFieldSubgroup