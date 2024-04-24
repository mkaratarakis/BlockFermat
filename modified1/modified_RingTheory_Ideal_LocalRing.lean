def maximalIdeal : Ideal R where
  carrier := nonunits R
  zero_mem' := zero_mem_nonunits.2 <| zero_ne_one
  add_mem' {_ _} hx hy := nonunits_add hx hy
  smul_mem' _ _ := mul_mem_nonunits_right
#align local_ring.maximal_ideal LocalRing.maximalIdeal

def ResidueField :=
  R ⧸ maximalIdeal R
#align local_ring.residue_field LocalRing.ResidueField

def residue : R →+* ResidueField R :=
  Ideal.Quotient.mk _
#align local_ring.residue LocalRing.residue

def lift {R S : Type*} [CommRing R] [LocalRing R] [Field S] (f : R →+* S) [IsLocalRingHom f] :
    LocalRing.ResidueField R →+* S :=
  Ideal.Quotient.lift _ f fun a ha =>
    by_contradiction fun h => ha (isUnit_of_map_unit f a (isUnit_iff_ne_zero.mpr h))
#align local_ring.residue_field.lift LocalRing.ResidueField.lift

def map (f : R →+* S) [IsLocalRingHom f] : ResidueField R →+* ResidueField S :=
  Ideal.Quotient.lift (maximalIdeal R) ((Ideal.Quotient.mk _).comp f) fun a ha => by
    erw [Ideal.Quotient.eq_zero_iff_mem]
    exact map_nonunit f a ha
#align local_ring.residue_field.map LocalRing.ResidueField.map

def mapEquiv (f : R ≃+* S) : LocalRing.ResidueField R ≃+* LocalRing.ResidueField S where
  toFun := map (f : R →+* S)
  invFun := map (f.symm : S →+* R)
  left_inv x := by simp only [map_map, RingEquiv.symm_comp, map_id, RingHom.id_apply]
  right_inv x := by simp only [map_map, RingEquiv.comp_symm, map_id, RingHom.id_apply]
  map_mul' := RingHom.map_mul _
  map_add' := RingHom.map_add _
#align local_ring.residue_field.map_equiv LocalRing.ResidueField.mapEquiv

def mapAut : RingAut R →* RingAut (LocalRing.ResidueField R) where
  toFun := mapEquiv
  map_mul' e₁ e₂ := mapEquiv_trans e₂ e₁
  map_one' := mapEquiv_refl
#align local_ring.residue_field.map_aut LocalRing.ResidueField.mapAut