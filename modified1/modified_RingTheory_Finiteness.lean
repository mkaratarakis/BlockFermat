def FG (N : Submodule R M) : Prop :=
  ∃ S : Finset M, Submodule.span R ↑S = N
#align submodule.fg Submodule.FG

def {N : Submodule R M} : N.FG ↔ ∃ S : Set M, S.Finite ∧ span R S = N :=
  ⟨fun ⟨t, h⟩ => ⟨_, Finset.finite_toSet t, h⟩, by
    rintro ⟨t', h, rfl⟩
    rcases Finite.exists_finset_coe h with ⟨t, rfl⟩
    exact ⟨t, rfl⟩⟩
#align submodule.fg_def Submodule.fg_def

def FG (I : Ideal R) : Prop :=
  ∃ S : Finset R, Ideal.span ↑S = I
#align ideal.fg Ideal.FG

def {R M} [Semiring R] [AddCommMonoid M] [Module R M] :
    Finite R M ↔ (⊤ : Submodule R M).FG :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩
#align module.finite_def Module.finite_def

def Finite (f : A →+* B) : Prop :=
  letI : Algebra A B := f.toAlgebra
  Module.Finite A B
#align ring_hom.finite RingHom.Finite

def Finite (f : A →ₐ[R] B) : Prop :=
  f.toRingHom.Finite
#align alg_hom.finite AlgHom.Finite