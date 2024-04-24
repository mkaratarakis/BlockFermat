def FG (S : Subalgebra R A) : Prop :=
  ∃ t : Finset A, Algebra.adjoin R ↑t = S
#align subalgebra.fg Subalgebra.FG

def {S : Subalgebra R A} : S.FG ↔ ∃ t : Set A, Set.Finite t ∧ Algebra.adjoin R t = S :=
  Iff.symm Set.exists_finite_iff_finset
#align subalgebra.fg_def Subalgebra.fg_def