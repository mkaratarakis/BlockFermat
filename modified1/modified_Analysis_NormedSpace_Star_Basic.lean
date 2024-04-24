def starNormedAddGroupHom : NormedAddGroupHom E E :=
  { starAddEquiv with bound' := ⟨1, fun _ => le_trans (norm_star _).le (one_mul _).symm.le⟩ }
#align star_normed_add_group_hom starNormedAddGroupHom

def starₗᵢ : E ≃ₗᵢ⋆[𝕜] E :=
  { starAddEquiv with
    map_smul' := star_smul
    norm_map' := norm_star }
#align starₗᵢ starₗᵢ