def degreeLE (n : WithBot ℕ) : Submodule R R[X] :=
  ⨅ k : ℕ, ⨅ _ : ↑k > n, LinearMap.ker (lcoeff R k)
#align polynomial.degree_le Polynomial.degreeLE

def degreeLT (n : ℕ) : Submodule R R[X] :=
  ⨅ k : ℕ, ⨅ (_ : k ≥ n), LinearMap.ker (lcoeff R k)
#align polynomial.degree_lt Polynomial.degreeLT

def degreeLTEquiv (R) [Semiring R] (n : ℕ) : degreeLT R n ≃ₗ[R] Fin n → R where
  toFun p n := (↑p : R[X]).coeff n
  invFun f :=
    ⟨∑ i : Fin n, monomial i (f i),
      (degreeLT R n).sum_mem fun i _ =>
        mem_degreeLT.mpr
          (lt_of_le_of_lt (degree_monomial_le i (f i)) (WithBot.coe_lt_coe.mpr i.is_lt))⟩
  map_add' p q := by
    ext
    dsimp
    rw [coeff_add]
  map_smul' x p := by
    ext
    dsimp
    rw [coeff_smul]
    rfl
  left_inv := by
    rintro ⟨p, hp⟩
    ext1
    simp only [Submodule.coe_mk]
    by_cases hp0 : p = 0
    · subst hp0
      simp only [coeff_zero, LinearMap.map_zero, Finset.sum_const_zero]
    rw [mem_degreeLT, degree_eq_natDegree hp0, Nat.cast_lt] at hp
    conv_rhs => rw [p.as_sum_range' n hp, ← Fin.sum_univ_eq_sum_range]
  right_inv f := by
    ext i
    simp only [finset_sum_coeff, Submodule.coe_mk]
    rw [Finset.sum_eq_single i, coeff_monomial, if_pos rfl]
    · rintro j - hji
      rw [coeff_monomial, if_neg]
      rwa [← Fin.ext_iff]
    · intro h
      exact (h (Finset.mem_univ _)).elim
#align polynomial.degree_lt_equiv Polynomial.degreeLTEquiv

def frange (p : R[X]) : Finset R :=
  letI := Classical.decEq R
  Finset.image (fun n => p.coeff n) p.support
#align polynomial.frange Polynomial.frange

def restriction (p : R[X]) : Polynomial (Subring.closure (↑p.frange : Set R)) :=
  ∑ i in p.support,
    monomial i
      (⟨p.coeff i,
          letI := Classical.decEq R
          if H : p.coeff i = 0 then H.symm ▸ (Subring.closure _).zero_mem
          else Subring.subset_closure (p.coeff_mem_frange _ H)⟩ :
        Subring.closure (↑p.frange : Set R))
#align polynomial.restriction Polynomial.restriction

def toSubring (hp : (↑p.frange : Set R) ⊆ T) : T[X] :=
  ∑ i in p.support,
    monomial i
      (⟨p.coeff i,
        letI := Classical.decEq R
        if H : p.coeff i = 0 then H.symm ▸ T.zero_mem else hp (p.coeff_mem_frange _ H)⟩ : T)
#align polynomial.to_subring Polynomial.toSubring

def ofSubring (p : T[X]) : R[X] :=
  ∑ i in p.support, monomial i (p.coeff i : R)
#align polynomial.of_subring Polynomial.ofSubring

def ofPolynomial (I : Ideal R[X]) : Submodule R R[X] where
  carrier := I.carrier
  zero_mem' := I.zero_mem
  add_mem' := I.add_mem
  smul_mem' c x H := by
    rw [← C_mul']
    exact I.mul_mem_left _ H
#align ideal.of_polynomial Ideal.ofPolynomial

def degreeLE (n : WithBot ℕ) : Submodule R R[X] :=
  Polynomial.degreeLE R n ⊓ I.ofPolynomial
#align ideal.degree_le Ideal.degreeLE

def leadingCoeffNth (n : ℕ) : Ideal R :=
  (I.degreeLE n).map <| lcoeff R n
#align ideal.leading_coeff_nth Ideal.leadingCoeffNth

def leadingCoeff : Ideal R :=
  ⨆ n : ℕ, I.leadingCoeffNth n
#align ideal.leading_coeff Ideal.leadingCoeff

structure from the `MvPolynomial.noZeroDivisors_fin`,
and then used to prove the general case without finiteness hypotheses.
See `MvPolynomial.noZeroDivisors` for the general case. -/
theorem noZeroDivisors_of_finite (R : Type u) (σ : Type v) [CommSemiring R] [Finite σ]
    [NoZeroDivisors R] : NoZeroDivisors (MvPolynomial σ R) := by
  cases nonempty_fintype σ
  haveI := noZeroDivisors_fin R (Fintype.card σ)
  exact (renameEquiv R (Fintype.equivFin σ)).injective.noZeroDivisors _ (map_zero _) (map_mul _)
#align mv_polynomial.no_zero_divisors_of_finite MvPolynomial.noZeroDivisors_of_finite