def MvPolynomial (σ : Type*) (R : Type*) [CommSemiring R] :=
  AddMonoidAlgebra R (σ →₀ ℕ)
#align mv_polynomial MvPolynomial

def monomial (s : σ →₀ ℕ) : R →ₗ[R] MvPolynomial σ R :=
  lsingle s
#align mv_polynomial.monomial MvPolynomial.monomial

def : p * q = p.sum fun m a => q.sum fun n b => monomial (m + n) (a * b) :=
  rfl
#align mv_polynomial.mul_def MvPolynomial.mul_def

def C : R →+* MvPolynomial σ R :=
  { singleZeroRingHom with toFun := monomial 0 }
#align mv_polynomial.C MvPolynomial.C

def X (n : σ) : MvPolynomial σ R :=
  monomial (Finsupp.single n 1) 1
#align mv_polynomial.X MvPolynomial.X

def a p).symm
#align mv_polynomial.C_mul' MvPolynomial.C_mul'

def monomialOneHom : Multiplicative (σ →₀ ℕ) →* MvPolynomial σ R :=
  AddMonoidAlgebra.of _ _
#align mv_polynomial.monomial_one_hom MvPolynomial.monomialOneHom

def support (p : MvPolynomial σ R) : Finset (σ →₀ ℕ) :=
  Finsupp.support p
#align mv_polynomial.support MvPolynomial.support

def coeff (m : σ →₀ ℕ) (p : MvPolynomial σ R) : R :=
  @DFunLike.coe ((σ →₀ ℕ) →₀ R) _ _ _ p m
  -- Porting note: I changed this from `@CoeFun.coe _ _ (MonoidAlgebra.coeFun _ _) p m` because
  -- I think it should work better syntactically. They are defeq.
#align mv_polynomial.coeff MvPolynomial.coeff

def {A} [AddCommMonoid A] {p : MvPolynomial σ R} {b : (σ →₀ ℕ) → R → A} :
    p.sum b = ∑ m in p.support, b m (p.coeff m) := by simp [support, Finsupp.sum, coeff]
#align mv_polynomial.sum_def MvPolynomial.sum_def

def coeffAddMonoidHom (m : σ →₀ ℕ) : MvPolynomial σ R →+ R
    where
  toFun := coeff m
  map_zero' := coeff_zero m
  map_add' := coeff_add m
#align mv_polynomial.coeff_add_monoid_hom MvPolynomial.coeffAddMonoidHom

def constantCoeff : MvPolynomial σ R →+* R
    where
  toFun := coeff 0
  map_one' := by simp [AddMonoidAlgebra.one_def]
  map_mul' := by classical simp [coeff_mul, Finsupp.support_single_ne_zero]
  map_zero' := coeff_zero _
  map_add' := coeff_add _
#align mv_polynomial.constant_coeff MvPolynomial.constantCoeff

def eval₂ (p : MvPolynomial σ R) : S₁ :=
  p.sum fun s a => f a * s.prod fun n e => g n ^ e
#align mv_polynomial.eval₂ MvPolynomial.eval₂

def eval₂Hom (f : R →+* S₁) (g : σ → S₁) : MvPolynomial σ R →+* S₁
    where
  toFun := eval₂ f g
  map_one' := eval₂_one _ _
  map_mul' _ _ := eval₂_mul _ _
  map_zero' := eval₂_zero f g
  map_add' _ _ := eval₂_add _ _
#align mv_polynomial.eval₂_hom MvPolynomial.eval₂Hom

def eval (f : σ → R) : MvPolynomial σ R →+* R :=
  eval₂Hom (RingHom.id _) f
#align mv_polynomial.eval MvPolynomial.eval

def map : MvPolynomial σ R →+* MvPolynomial σ S₁ :=
  eval₂Hom (C.comp f) X
#align mv_polynomial.map MvPolynomial.map

def mapAlgHom [CommSemiring S₂] [Algebra R S₁] [Algebra R S₂] (f : S₁ →ₐ[R] S₂) :
    MvPolynomial σ S₁ →ₐ[R] MvPolynomial σ S₂ :=
  { map (↑f : S₁ →+* S₂) with
    commutes' := fun r => by
      have h₁ : algebraMap R (MvPolynomial σ S₁) r = C (algebraMap R S₁ r) := rfl
      have h₂ : algebraMap R (MvPolynomial σ S₂) r = C (algebraMap R S₂ r) := rfl
      simp_rw [OneHom.toFun_eq_coe]
      -- Porting note: we're missing some `simp` lemmas like `MonoidHom.coe_toOneHom`
      change @DFunLike.coe (_ →+* _) _ _ _ _ _ = _
      rw [h₁, h₂, map, eval₂Hom_C, RingHom.comp_apply, AlgHom.coe_toRingHom, AlgHom.commutes] }
#align mv_polynomial.map_alg_hom MvPolynomial.mapAlgHom

def aeval : MvPolynomial σ R →ₐ[R] S₁ :=
  { eval₂Hom (algebraMap R S₁) f with commutes' := fun _r => eval₂_C _ _ _ }
#align mv_polynomial.aeval MvPolynomial.aeval

def (p : MvPolynomial σ R) : aeval f p = eval₂ (algebraMap R S₁) f p :=
  rfl
#align mv_polynomial.aeval_def MvPolynomial.aeval_def

def aevalTower (f : R →ₐ[S] A) (X : σ → A) : MvPolynomial σ R →ₐ[S] A :=
  { eval₂Hom (↑f) X with
    commutes' := fun r => by
      simp [IsScalarTower.algebraMap_eq S R (MvPolynomial σ R), algebraMap_eq] }
#align mv_polynomial.aeval_tower MvPolynomial.aevalTower