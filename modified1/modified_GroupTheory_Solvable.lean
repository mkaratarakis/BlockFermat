def derivedSeries : ℕ → Subgroup G
  | 0 => ⊤
  | n + 1 => ⁅derivedSeries n, derivedSeries n⁆
#align derived_series derivedSeries

def isSolvable_def

instance (priority := 100) CommGroup.isSolvable {G : Type*} [CommGroup G] : IsSolvable G :=
  ⟨⟨1, le_bot_iff.mp (Abelianization.commutator_subset_ker (MonoidHom.id G))⟩⟩
#align comm_group.is_solvable CommGroup.isSolvable

def _).mp
    (not_exists_of_forall_not fun n h =>
      h1 (Subgroup.mem_bot.mp ((congr_arg (Membership.mem g) h).mp (h2 n))))
#align not_solvable_of_mem_derived_series not_solvable_of_mem_derivedSeries