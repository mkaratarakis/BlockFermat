def AffineMap.restrict (φ : P₁ →ᵃ[k] P₂) {E : AffineSubspace k P₁} {F : AffineSubspace k P₂}
    [Nonempty E] [Nonempty F] (hEF : E.map φ ≤ F) : E →ᵃ[k] F := by
  refine' ⟨_, _, _⟩
  · exact fun x => ⟨φ x, hEF <| AffineSubspace.mem_map.mpr ⟨x, x.property, rfl⟩⟩
  · refine' φ.linear.restrict (_ : E.direction ≤ F.direction.comap φ.linear)
    rw [← Submodule.map_le_iff_le_comap, ← AffineSubspace.map_direction]
    exact AffineSubspace.direction_le hEF
  · intro p v
    simp only [Subtype.ext_iff, Subtype.coe_mk, AffineSubspace.coe_vadd]
    apply AffineMap.map_vadd
#align affine_map.restrict AffineMap.restrict