def ringExpChar (R : Type*) [NonAssocSemiring R] : ℕ := max (ringChar R) 1

theorem ringExpChar.eq (q : ℕ) [h : ExpChar R q] : ringExpChar R = q := by
  cases' h with _ _ h _
  · haveI := CharP.ofCharZero R
    rw [ringExpChar, ringChar.eq R 0]; rfl
  rw [ringExpChar, ringChar.eq R q]
  exact Nat.max_eq_left h.one_lt.le

@[simp]
theorem ringExpChar.eq_one (R : Type*) [NonAssocSemiring R] [CharZero R] : ringExpChar R = 1 := by
  rw [ringExpChar, ringChar.eq_zero, max_eq_right zero_le_one]

/-- The exponential characteristic is one if the characteristic is zero. -/
theorem expChar_one_of_char_zero (q : ℕ) [hp : CharP R 0] [hq : ExpChar R q] : q = 1 := by
  cases' hq with q hq_one hq_prime hq_hchar
  · rfl
  · exact False.elim <| hq_prime.ne_zero <| hq_hchar.eq R hp
#align exp_char_one_of_char_zero expChar_one_of_char_zero

def frobenius : R →+* R where
  __ := powMonoidHom p
  map_zero' := zero_pow (expChar_pos R p).ne'
  map_add' := add_pow_expChar R
#align frobenius frobenius

def iterateFrobenius : R →+* R where
  __ := powMonoidHom (p ^ n)
  map_zero' := zero_pow (expChar_pow_pos R p n).ne'
  map_add' := add_pow_expChar_pow R

variable {R}

theorem frobenius_def : frobenius R p x = x ^ p := rfl
#align frobenius_def frobenius_def

def : iterateFrobenius R p n x = x ^ p ^ n := rfl

theorem iterate_frobenius : (frobenius R p)^[n] x = x ^ p ^ n := congr_fun (pow_iterate p n) x
#align iterate_frobenius iterate_frobenius

def LinearMap.frobenius [Algebra R S] : S →ₛₗ[frobenius R p] S where
  __ := frobenius S p
  map_smul' r s := show frobenius S p _ = _ by
    simp_rw [Algebra.smul_def, map_mul, ← (algebraMap R S).map_frobenius]; rfl

/-- The iterated frobenius map of an algebra as a iterated-frobenius-semilinear map. -/
nonrec def LinearMap.iterateFrobenius [Algebra R S] : S →ₛₗ[iterateFrobenius R p n] S where
  __ := iterateFrobenius S p n
  map_smul' f s := show iterateFrobenius S p n _ = _ by
    simp_rw [iterateFrobenius_def, Algebra.smul_def, mul_pow, ← map_pow]; rfl

theorem LinearMap.frobenius_def [Algebra R S] (x : S) : frobenius R S p x = x ^ p := rfl

theorem LinearMap.iterateFrobenius_def [Algebra R S] (n : ℕ) (x : S) :
    iterateFrobenius R S p n x = x ^ p ^ n := rfl

theorem frobenius_zero : frobenius R p 0 = 0 :=
  (frobenius R p).map_zero
#align frobenius_zero frobenius_zero