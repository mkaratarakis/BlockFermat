def LinearEquiv.ofLiftRankEq
    (cond : Cardinal.lift.{v'} (Module.rank R M) = Cardinal.lift.{v} (Module.rank R M')) :
    M ≃ₗ[R] M' :=
  Classical.choice (nonempty_linearEquiv_of_lift_rank_eq cond)
#align linear_equiv.of_lift_rank_eq LinearEquiv.ofLiftRankEq

def LinearEquiv.ofRankEq (cond : Module.rank R M = Module.rank R M₁) : M ≃ₗ[R] M₁ :=
  Classical.choice (nonempty_linearEquiv_of_rank_eq cond)
#align linear_equiv.of_rank_eq LinearEquiv.ofRankEq

def LinearEquiv.ofFinrankEq [Module.Finite R M] [Module.Finite R M']
    (cond : finrank R M = finrank R M') : M ≃ₗ[R] M' :=
  Classical.choice <| FiniteDimensional.nonempty_linearEquiv_of_finrank_eq cond
#align linear_equiv.of_finrank_eq LinearEquiv.ofFinrankEq

def finBasis [Module.Finite R M] :
    Basis (Fin (finrank R M)) R M :=
  (Module.Free.chooseBasis R M).reindex (Fintype.equivFinOfCardEq
    (finrank_eq_card_chooseBasisIndex R M).symm)
#align finite_dimensional.fin_basis FiniteDimensional.finBasis

def finBasisOfFinrankEq [Module.Finite R M]
    {n : ℕ} (hn : finrank R M = n) :
    Basis (Fin n) R M :=
  (finBasis R M).reindex (Fin.castIso hn).toEquiv
#align finite_dimensional.fin_basis_of_finrank_eq FiniteDimensional.finBasisOfFinrankEq

def basisUnique (ι : Type*) [Unique ι]
    (h : finrank R M = 1) :
    Basis ι R M :=
  haveI : Module.Finite R M :=
    Module.finite_of_finrank_pos (_root_.zero_lt_one.trans_le h.symm.le)
  (finBasisOfFinrankEq R M h).reindex (Equiv.equivOfUnique _ _)
#align finite_dimensional.basis_unique FiniteDimensional.basisUnique