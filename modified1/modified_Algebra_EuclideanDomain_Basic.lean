def P (a b : R) : R × R × R → Prop
  | (r, s, t) => (r : R) = a * s + b * t

theorem xgcdAux_P (a b : R) {r r' : R} {s t s' t'} (p : P a b (r, s, t))
    (p' : P a b (r', s', t')) : P a b (xgcdAux r s t r' s' t') := by
  induction r, r' using GCD.induction generalizing s t s' t' with
  | H0 n => simpa only [xgcd_zero_left]
  | H1 _ _ h IH =>
    rw [xgcdAux_rec h]
    refine' IH _ p
    unfold P at p p' ⊢
    dsimp
    rw [mul_sub, mul_sub, add_sub, sub_add_eq_add_sub, ← p', sub_sub, mul_comm _ s, ← mul_assoc,
      mul_comm _ t, ← mul_assoc, ← add_mul, ← p, mod_eq_sub_mul_div]
set_option linter.uppercaseLean3 false in
#align euclidean_domain.xgcd_aux_P EuclideanDomain.xgcdAux_P