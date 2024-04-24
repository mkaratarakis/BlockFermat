def IsInvariantSubring.subtypeHom : U →+*[M] R' :=
  { U.subtype with map_smul' := fun _ _ ↦ rfl }
#align is_invariant_subring.subtype_hom IsInvariantSubring.subtypeHom