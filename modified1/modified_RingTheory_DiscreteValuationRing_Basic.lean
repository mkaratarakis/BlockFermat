def HasUnitMulPowIrreducibleFactorization [CommRing R] : Prop :=
  ∃ p : R, Irreducible p ∧ ∀ {x : R}, x ≠ 0 → ∃ n : ℕ, Associated (p ^ n) x
#align discrete_valuation_ring.has_unit_mul_pow_irreducible_factorization DiscreteValuationRing.HasUnitMulPowIrreducibleFactorization

def addVal (R : Type u) [CommRing R] [IsDomain R] [DiscreteValuationRing R] :
    AddValuation R PartENat :=
  addValuation (Classical.choose_spec (exists_prime R))
#align discrete_valuation_ring.add_val DiscreteValuationRing.addVal

def (r : R) (u : Rˣ) {ϖ : R} (hϖ : Irreducible ϖ) (n : ℕ) (hr : r = u * ϖ ^ n) :
    addVal R r = n := by
  rw [addVal, addValuation_apply, hr, eq_of_associated_left
      (associated_of_irreducible R hϖ (Classical.choose_spec (exists_prime R)).irreducible),
    eq_of_associated_right (Associated.symm ⟨u, mul_comm _ _⟩),
    multiplicity_pow_self_of_prime (irreducible_iff_prime.1 hϖ)]
#align discrete_valuation_ring.add_val_def DiscreteValuationRing.addVal_def

def _ u hϖ n rfl
#align discrete_valuation_ring.add_val_def' DiscreteValuationRing.addVal_def'

def ϖ 1 hϖ 1
#align discrete_valuation_ring.add_val_uniformizer DiscreteValuationRing.addVal_uniformizer