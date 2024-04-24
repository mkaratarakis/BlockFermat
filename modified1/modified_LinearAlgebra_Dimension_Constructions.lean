def finDimVectorspaceEquiv (n : ℕ) (hn : Module.rank R M = n) : M ≃ₗ[R] Fin n → R := by
  haveI := nontrivial_of_invariantBasisNumber R
  have : Cardinal.lift.{u} (n : Cardinal.{v}) = Cardinal.lift.{v} (n : Cardinal.{u}) := by simp
  have hn := Cardinal.lift_inj.{v, u}.2 hn
  rw [this] at hn
  rw [← @rank_fin_fun R _ _ n] at hn
  haveI : Module.Free R (Fin n → R) := Module.Free.pi _ _
  exact Classical.choice (nonempty_linearEquiv_of_lift_rank_eq hn)
#align fin_dim_vectorspace_equiv finDimVectorspaceEquiv

def Set.finrank (s : Set M) : ℕ :=
  finrank R (span R s)
#align set.finrank Set.finrank