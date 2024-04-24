def divX (p : R[X]) : R[X] :=
  ⟨AddMonoidAlgebra.divOf p.toFinsupp 1⟩
set_option linter.uppercaseLean3 false in
#align polynomial.div_X Polynomial.divX

def divX_hom : R[X] →+ R[X] :=
  { toFun := divX
    map_zero' := divX_zero
    map_add' := fun _ _ => divX_add }

@[simp] theorem divX_hom_toFun : divX_hom p = divX p := rfl

theorem natDegree_divX_eq_natDegree_tsub_one : p.divX.natDegree = p.natDegree - 1 := by
  apply map_natDegree_eq_sub (φ := divX_hom)
  · intro f
    simpa [divX_hom, divX_eq_zero_iff] using eq_C_of_natDegree_eq_zero
  · intros n c c0
    rw [← C_mul_X_pow_eq_monomial, divX_hom_toFun, divX_C_mul, divX_X_pow]
    split_ifs with n0
    · simp [n0]
    · exact natDegree_C_mul_X_pow (n - 1) c c0

theorem natDegree_divX_le : p.divX.natDegree ≤ p.natDegree :=
  natDegree_divX_eq_natDegree_tsub_one.trans_le (Nat.pred_le _)

theorem divX_C_mul_X_pow : divX (C a * X ^ n) = if n = 0 then 0 else C a * X ^ (n - 1) := by
  simp only [divX_C_mul, divX_X_pow, mul_ite, mul_zero]

theorem degree_divX_lt (hp0 : p ≠ 0) : (divX p).degree < p.degree := by
  haveI := Nontrivial.of_polynomial_ne hp0
  calc
    degree (divX p) < (divX p * X + C (p.coeff 0)).degree :=
      if h : degree p ≤ 0 then by
        have h' : C (p.coeff 0) ≠ 0 := by rwa [← eq_C_of_degree_le_zero h]
        rw [eq_C_of_degree_le_zero h, divX_C, degree_zero, zero_mul, zero_add]
        exact lt_of_le_of_ne bot_le (Ne.symm (mt degree_eq_bot.1 <| by simpa using h'))
      else by
        have hXp0 : divX p ≠ 0 := by
          simpa [divX_eq_zero_iff, -not_le, degree_le_zero_iff] using h
        have : leadingCoeff (divX p) * leadingCoeff X ≠ 0 := by simpa
        have : degree (C (p.coeff 0)) < degree (divX p * X) :=
          calc
            degree (C (p.coeff 0)) ≤ 0 := degree_C_le
            _ < 1 := by decide
            _ = degree (X : R[X]) := degree_X.symm
            _ ≤ degree (divX p * X) := by
              rw [← zero_add (degree X), degree_mul' this]
              exact add_le_add
                (by rw [zero_le_degree_iff, Ne, divX_eq_zero_iff]
                    exact fun h0 => h (h0.symm ▸ degree_C_le))
                    le_rfl
        rw [degree_add_eq_left_of_degree_lt this]; exact degree_lt_degree_mul_X hXp0
    _ = degree p := congr_arg _ (divX_mul_X_add _)
set_option linter.uppercaseLean3 false in
#align polynomial.degree_div_X_lt Polynomial.degree_divX_lt

def recOnHorner {M : R[X] → Sort*} (p : R[X]) (M0 : M 0)
    (MC : ∀ p a, coeff p 0 = 0 → a ≠ 0 → M p → M (p + C a))
    (MX : ∀ p, p ≠ 0 → M p → M (p * X)) : M p :=
  letI := Classical.decEq R
  if hp : p = 0 then hp ▸ M0
  else by
    have wf : degree (divX p) < degree p := degree_divX_lt hp
    rw [← divX_mul_X_add p] at *
    exact
      if hcp0 : coeff p 0 = 0 then by
        rw [hcp0, C_0, add_zero]
        exact
          MX _ (fun h : divX p = 0 => by simp [h, hcp0] at hp) (recOnHorner (divX p) M0 MC MX)
      else
        MC _ _ (coeff_mul_X_zero _) hcp0
          (if hpX0 : divX p = 0 then show M (divX p * X) by rw [hpX0, zero_mul]; exact M0
          else MX (divX p) hpX0 (recOnHorner _ M0 MC MX))
termination_by p.degree
#align polynomial.rec_on_horner Polynomial.recOnHorner