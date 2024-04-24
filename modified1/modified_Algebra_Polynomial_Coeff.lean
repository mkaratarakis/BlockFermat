def lsum {R A M : Type*} [Semiring R] [Semiring A] [AddCommMonoid M] [Module R A] [Module R M]
    (f : ℕ → A →ₗ[R] M) : A[X] →ₗ[R] M
    where
  toFun p := p.sum (f · ·)
  map_add' p q := sum_add_index p q _ (fun n => (f n).map_zero) fun n _ _ => (f n).map_add _ _
  map_smul' c p := by
    -- Porting note: added `dsimp only`; `beta_reduce` alone is not sufficient
    dsimp only
    rw [sum_eq_of_subset (f · ·) (fun n => (f n).map_zero) (support_smul c p)]
    simp only [sum_def, Finset.smul_sum, coeff_smul, LinearMap.map_smul, RingHom.id_apply]
#align polynomial.lsum Polynomial.lsum

def lcoeff (n : ℕ) : R[X] →ₗ[R] R where
  toFun p := coeff p n
  map_add' p q := coeff_add p q n
  map_smul' r p := coeff_smul r p n
#align polynomial.lcoeff Polynomial.lcoeff

def constantCoeff : R[X] →+* R where
  toFun p := coeff p 0
  map_one' := coeff_one_zero
  map_mul' := mul_coeff_zero
  map_zero' := coeff_zero 0
  map_add' p q := coeff_add p q 0
#align polynomial.constant_coeff Polynomial.constantCoeff