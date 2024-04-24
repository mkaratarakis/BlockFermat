def finsuppLEquivDirectSum : (ι →₀ M) ≃ₗ[R] ⨁ _ : ι, M :=
  haveI : ∀ m : M, Decidable (m ≠ 0) := Classical.decPred _
  finsuppLequivDFinsupp R
#align finsupp_lequiv_direct_sum finsuppLEquivDirectSum