def finrank (R M : Type*) [Semiring R] [AddCommGroup M] [Module R M] : ℕ :=
  Cardinal.toNat (Module.rank R M)
#align finite_dimensional.finrank FiniteDimensional.finrank