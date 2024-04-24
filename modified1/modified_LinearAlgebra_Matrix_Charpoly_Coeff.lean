def (trace M), ← C_eq_algebraMap, pow_two, ← mul_assoc, add_assoc,
    ← add_mul, ← coeff_det_one_add_X_smul_one, ← coeff_divX, add_comm (C _), divX_mul_X_add,
    add_comm (1 : R[X]), ← C.map_one]
  convert (divX_mul_X_add _).symm
  rw [coeff_zero_eq_eval_zero, eval_det_add_X_smul, det_one, eval_one]

/-- The first two terms of the taylor expansion of `det (1 + r • M)` at `r = 0`. -/
lemma det_one_add_smul (r : R) (M : Matrix n n R) :
    det (1 + r • M) =
      1 + trace M * r + (det (1 + (X : R[X]) • M.map C)).divX.divX.eval r * r ^ 2 := by
  simpa [eval_det, ← smul_eq_mul_diagonal] using congr_arg (eval r) (Matrix.det_one_add_X_smul M)

end Matrix

variable {p : ℕ} [Fact p.Prime]

theorem matPolyEquiv_eq_X_pow_sub_C {K : Type*} (k : ℕ) [Field K] (M : Matrix n n K) :
    matPolyEquiv ((expand K k : K[X] →+* K[X]).mapMatrix (charmatrix (M ^ k))) =
      X ^ k - C (M ^ k) := by
  -- Porting note: `i` and `j` are used later on, but were not mentioned in mathlib3
  ext m i j
  rw [coeff_sub, coeff_C, matPolyEquiv_coeff_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
    AlgHom.coe_toRingHom, DMatrix.sub_apply, coeff_X_pow]
  by_cases hij : i = j
  · rw [hij, charmatrix_apply_eq, AlgHom.map_sub, expand_C, expand_X, coeff_sub, coeff_X_pow,
      coeff_C]
                             -- Porting note: the second `Matrix.` was `DMatrix.`
    split_ifs with mp m0 <;> simp only [Matrix.one_apply_eq, Matrix.zero_apply]
  · rw [charmatrix_apply_ne _ _ _ hij, AlgHom.map_neg, expand_C, coeff_neg, coeff_C]
    split_ifs with m0 mp <;>
      -- Porting note: again, the first `Matrix.` that was `DMatrix.`
      simp only [hij, zero_sub, Matrix.zero_apply, sub_zero, neg_zero, Matrix.one_apply_ne, Ne,
        not_false_iff]
set_option linter.uppercaseLean3 false in
#align mat_poly_equiv_eq_X_pow_sub_C matPolyEquiv_eq_X_pow_sub_C