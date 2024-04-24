def mapToFractionRing (B : Type*) [CommRing B] [Algebra A B] [IsLocalization S B]
    (hS : S ≤ A⁰) : B →ₐ[A] K :=
  { IsLocalization.lift (map_isUnit_of_le K S hS) with commutes' := fun a => by simp }
#align localization.map_to_fraction_ring Localization.mapToFractionRing

def subalgebra (hS : S ≤ A⁰) : Subalgebra A K :=
  (mapToFractionRing K S (Localization S) hS).range.copy
      { x | ∃ (a s : A) (hs : s ∈ S), x = IsLocalization.mk' K a ⟨s, hS hs⟩ } <| by
    ext
    symm
    apply mem_range_mapToFractionRing_iff
#align localization.subalgebra Localization.subalgebra

def ofField : Subalgebra A K :=
  (mapToFractionRing K S (Localization S) hS).range.copy
      { x | ∃ (a s : A) (_ : s ∈ S), x = algebraMap A K a * (algebraMap A K s)⁻¹ } <| by
    ext
    symm
    apply mem_range_mapToFractionRing_iff_ofField
#align localization.subalgebra.of_field Localization.subalgebra.ofField