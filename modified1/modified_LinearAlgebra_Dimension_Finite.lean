def Basis.fintypeIndexOfRankLtAleph0 {ι : Type*} (b : Basis ι R M)
    (h : Module.rank R M < ℵ₀) : Fintype ι :=
  Classical.choice (b.nonempty_fintype_index_of_rank_lt_aleph0 h)
#align basis.fintype_index_of_rank_lt_aleph_0 Basis.fintypeIndexOfRankLtAleph0

def R M))
  obtain ⟨t, ht, ht'⟩ := le_mk_iff_exists_subset.mp hs'.le
  exact ⟨t, ht', .mono ht hs⟩

lemma exists_finset_linearIndependent_of_le_rank {n : ℕ} (hn : n ≤ Module.rank R M) :
    ∃ s : Finset M, s.card = n ∧ LinearIndependent R ((↑) : s → M) := by
  have := nonempty_linearIndependent_set
  cases' hn.eq_or_lt with h h
  · obtain ⟨⟨s, hs⟩, hs'⟩ := Cardinal.exists_eq_natCast_of_iSup_eq _
      (Cardinal.bddAbove_range.{v, v} _) _ (h.trans (Module.rank_def R M)).symm
    have : Finite s := lt_aleph0_iff_finite.mp (hs' ▸ nat_lt_aleph0 n)
    cases nonempty_fintype s
    exact ⟨s.toFinset, by simpa using hs', by convert hs <;> exact Set.mem_toFinset⟩
  · obtain ⟨s, hs, hs'⟩ := exists_set_linearIndependent_of_lt_rank h
    have : Finite s := lt_aleph0_iff_finite.mp (hs ▸ nat_lt_aleph0 n)
    cases nonempty_fintype s
    exact ⟨s.toFinset, by simpa using hs, by convert hs' <;> exact Set.mem_toFinset⟩

lemma exists_linearIndependent_of_le_rank {n : ℕ} (hn : n ≤ Module.rank R M) :
    ∃ f : Fin n → M, LinearIndependent R f :=
  have ⟨_, hs, hs'⟩ := exists_finset_linearIndependent_of_le_rank hn
  ⟨_, (linearIndependent_equiv (Finset.equivFinOfCardEq hs).symm).mpr hs'⟩

lemma natCast_le_rank_iff {n : ℕ} :
    n ≤ Module.rank R M ↔ ∃ f : Fin n → M, LinearIndependent R f :=
  ⟨exists_linearIndependent_of_le_rank,
    fun H ↦ by simpa using H.choose_spec.cardinal_lift_le_rank⟩

lemma natCast_le_rank_iff_finset {n : ℕ} :
    n ≤ Module.rank R M ↔ ∃ s : Finset M, s.card = n ∧ LinearIndependent R ((↑) : s → M) :=
  ⟨exists_finset_linearIndependent_of_le_rank,
    fun ⟨s, h₁, h₂⟩ ↦ by simpa [h₁] using h₂.cardinal_le_rank⟩

lemma exists_finset_linearIndependent_of_le_finrank {n : ℕ} (hn : n ≤ finrank R M) :
    ∃ s : Finset M, s.card = n ∧ LinearIndependent R ((↑) : s → M) := by
  by_cases h : finrank R M = 0
  · rw [le_zero_iff.mp (hn.trans_eq h)]
    exact ⟨∅, rfl, by convert linearIndependent_empty R M using 2 <;> aesop⟩
  exact exists_finset_linearIndependent_of_le_rank
    ((natCast_le.mpr hn).trans_eq (cast_toNat_of_lt_aleph0 (toNat_ne_zero.mp h).2))

lemma exists_linearIndependent_of_le_finrank {n : ℕ} (hn : n ≤ finrank R M) :
    ∃ f : Fin n → M, LinearIndependent R f :=
  have ⟨_, hs, hs'⟩ := exists_finset_linearIndependent_of_le_finrank hn
  ⟨_, (linearIndependent_equiv (Finset.equivFinOfCardEq hs).symm).mpr hs'⟩

variable [Module.Finite R M]

theorem Module.Finite.not_linearIndependent_of_infinite {ι : Type*} [Infinite ι]
    (v : ι → M) : ¬LinearIndependent R v := mt LinearIndependent.finite <| @not_finite _ _
#align finite_dimensional.not_linear_independent_of_infinite Module.Finite.not_linearIndependent_of_infinite

def CompleteLattice.Independent.fintypeNeBotOfFiniteDimensional
    {p : ι → Submodule R M} (hp : CompleteLattice.Independent p) :
    Fintype { i : ι // p i ≠ ⊥ } := by
  suffices #{ i // p i ≠ ⊥ } < (ℵ₀ : Cardinal.{w}) by