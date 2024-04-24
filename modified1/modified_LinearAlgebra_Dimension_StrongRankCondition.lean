def Basis.indexEquiv (v : Basis ι R M) (v' : Basis ι' R M) : ι ≃ ι' :=
  (Cardinal.lift_mk_eq'.1 <| mk_eq_mk_of_basis v v').some
#align basis.index_equiv Basis.indexEquiv

def Submodule.inductionOnRank [IsDomain R] [Finite ι] (b : Basis ι R M)
    (P : Submodule R M → Sort*) (ih : ∀ N : Submodule R M,
    (∀ N' ≤ N, ∀ x ∈ N, (∀ (c : R), ∀ y ∈ N', c • x + y = (0 : M) → c = 0) → P N') → P N)
    (N : Submodule R M) : P N :=
  letI := Fintype.ofFinite ι
  Submodule.inductionOnRankAux b P ih (Fintype.card ι) N fun hs hli => by
    simpa using b.card_le_card_of_linearIndependent hli
#align submodule.induction_on_rank Submodule.inductionOnRank

def Basis.unique {ι : Type*} (b : Basis ι R R) : Unique ι := by
  have A : Cardinal.mk ι = ↑(FiniteDimensional.finrank R R) :=
    (Module.mk_finrank_eq_card_basis b).symm
  -- Porting note: replace `algebraMap.coe_one` with `Nat.cast_one`
  simp only [Cardinal.eq_one_iff_unique, FiniteDimensional.finrank_self, Nat.cast_one] at A
  exact Nonempty.some ((unique_iff_subsingleton_and_nonempty _).2 A)
#align basis.unique Basis.unique