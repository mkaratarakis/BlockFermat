def TopologicalSpace.PositiveCompacts.Icc01 : PositiveCompacts ℝ where
  carrier := Icc 0 1
  isCompact' := isCompact_Icc
  interior_nonempty' := by simp_rw [interior_Icc, nonempty_Ioo, zero_lt_one]
#align topological_space.positive_compacts.Icc01 TopologicalSpace.PositiveCompacts.Icc01

def TopologicalSpace.PositiveCompacts.piIcc01 (ι : Type*) [Finite ι] :
    PositiveCompacts (ι → ℝ) where
  carrier := pi univ fun _ => Icc 0 1
  isCompact' := isCompact_univ_pi fun _ => isCompact_Icc
  interior_nonempty' := by
    simp only [interior_pi_set, Set.toFinite, interior_Icc, univ_pi_nonempty_iff, nonempty_Ioo,
      imp_true_iff, zero_lt_one]
#align topological_space.positive_compacts.pi_Icc01 TopologicalSpace.PositiveCompacts.piIcc01

def _root_.AlternatingMap.measure (ω : G [⋀^Fin n]→ₗ[ℝ] ℝ) :
    Measure G :=
  ‖ω (finBasisOfFinrankEq ℝ G _i.out)‖₊ • (finBasisOfFinrankEq ℝ G _i.out).addHaar
#align alternating_map.measure AlternatingMap.measure