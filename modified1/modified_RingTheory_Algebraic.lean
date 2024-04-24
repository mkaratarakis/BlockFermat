def IsAlgebraic (x : A) : Prop :=
  ∃ p : R[X], p ≠ 0 ∧ aeval x p = 0
#align is_algebraic IsAlgebraic

def Transcendental (x : A) : Prop :=
  ¬IsAlgebraic R x
#align transcendental Transcendental

def Subalgebra.IsAlgebraic (S : Subalgebra R A) : Prop :=
  ∀ x ∈ S, IsAlgebraic R x
#align subalgebra.is_algebraic Subalgebra.IsAlgebraic

def Algebra.IsAlgebraic : Prop :=
  ∀ x : A, IsAlgebraic R x
#align algebra.is_algebraic Algebra.IsAlgebraic

def algEquivEquivAlgHom (ha : Algebra.IsAlgebraic K L) :
    (L ≃ₐ[K] L) ≃* (L →ₐ[K] L) where
  toFun ϕ := ϕ.toAlgHom
  invFun ϕ := AlgEquiv.ofBijective ϕ (ha.algHom_bijective ϕ)
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl
  map_mul' _ _ := rfl
#align algebra.is_algebraic.alg_equiv_equiv_alg_hom Algebra.IsAlgebraic.algEquivEquivAlgHom

def algEquivEquivAlgHom [FiniteDimensional K L] :
    (L ≃ₐ[K] L) ≃* (L →ₐ[K] L) :=
  (Algebra.IsAlgebraic.of_finite K L).algEquivEquivAlgHom K L
#align alg_equiv_equiv_alg_hom algEquivEquivAlgHom

def Polynomial.hasSMulPi [Semiring R'] [SMul R' S'] : SMul R'[X] (R' → S') :=
  ⟨fun p f x => eval x p • f x⟩
#align polynomial.has_smul_pi Polynomial.hasSMulPi

def Polynomial.hasSMulPi' [CommSemiring R'] [Semiring S'] [Algebra R' S']
    [SMul S' T'] : SMul R'[X] (S' → T') :=
  ⟨fun p f x => aeval x p • f x⟩
#align polynomial.has_smul_pi' Polynomial.hasSMulPi'

def Polynomial.algebraPi : Algebra R'[X] (S' → T') :=
  { Polynomial.hasSMulPi' R' S' T' with
    toFun := fun p z => algebraMap S' T' (aeval z p)
    map_one' := by
      funext z
      simp only [Polynomial.aeval_one, Pi.one_apply, map_one]
    map_mul' := fun f g => by
      funext z
      simp only [Pi.mul_apply, map_mul]
    map_zero' := by
      funext z
      simp only [Polynomial.aeval_zero, Pi.zero_apply, map_zero]
    map_add' := fun f g => by
      funext z
      simp only [Polynomial.aeval_add, Pi.add_apply, map_add]
    commutes' := fun p f => by
      funext z
      exact mul_comm _ _
    smul_def' := fun p f => by
      funext z
      simp only [polynomial_smul_apply', Algebra.algebraMap_eq_smul_one, RingHom.coe_mk,
        MonoidHom.coe_mk, OneHom.coe_mk, Pi.mul_apply, Algebra.smul_mul_assoc, one_mul] }
#align polynomial.algebra_pi Polynomial.algebraPi