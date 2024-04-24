def frobeniusEquiv : R ≃+* R :=
  RingEquiv.ofBijective (frobenius R p) PerfectRing.bijective_frobenius
#align frobenius_equiv frobeniusEquiv

def (x : R) : frobeniusEquiv R p x = x ^ p := rfl

/-- The iterated Frobenius automorphism for a perfect ring. -/
@[simps! apply]
noncomputable def iterateFrobeniusEquiv : R ≃+* R :=
  RingEquiv.ofBijective (iterateFrobenius R p n) (bijective_iterateFrobenius R p n)

@[simp]
theorem coe_iterateFrobeniusEquiv : ⇑(iterateFrobeniusEquiv R p n) = iterateFrobenius R p n := rfl

theorem iterateFrobeniusEquiv_def (x : R) : iterateFrobeniusEquiv R p n x = x ^ p ^ n := rfl

theorem iterateFrobeniusEquiv_add_apply (x : R) : iterateFrobeniusEquiv R p (m + n) x =
    iterateFrobeniusEquiv R p m (iterateFrobeniusEquiv R p n x) :=
  iterateFrobenius_add_apply R p m n x

theorem iterateFrobeniusEquiv_add : iterateFrobeniusEquiv R p (m + n) =
    (iterateFrobeniusEquiv R p n).trans (iterateFrobeniusEquiv R p m) :=
  RingEquiv.ext (iterateFrobeniusEquiv_add_apply R p m n)

theorem iterateFrobeniusEquiv_symm_add_apply (x : R) : (iterateFrobeniusEquiv R p (m + n)).symm x =
    (iterateFrobeniusEquiv R p m).symm ((iterateFrobeniusEquiv R p n).symm x) :=
  (iterateFrobeniusEquiv R p (m + n)).injective <| by rw [RingEquiv.apply_symm_apply, add_comm,
    iterateFrobeniusEquiv_add_apply, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

theorem iterateFrobeniusEquiv_symm_add : (iterateFrobeniusEquiv R p (m + n)).symm =
    (iterateFrobeniusEquiv R p n).symm.trans (iterateFrobeniusEquiv R p m).symm :=
  RingEquiv.ext (iterateFrobeniusEquiv_symm_add_apply R p m n)

theorem iterateFrobeniusEquiv_zero_apply (x : R) : iterateFrobeniusEquiv R p 0 x = x := by
  rw [iterateFrobeniusEquiv_def, pow_zero, pow_one]

theorem iterateFrobeniusEquiv_one_apply (x : R) : iterateFrobeniusEquiv R p 1 x = x ^ p := by
  rw [iterateFrobeniusEquiv_def, pow_one]

@[simp]
theorem iterateFrobeniusEquiv_zero  : iterateFrobeniusEquiv R p 0 = RingEquiv.refl R :=
  RingEquiv.ext (iterateFrobeniusEquiv_zero_apply R p)

@[simp]
theorem iterateFrobeniusEquiv_one : iterateFrobeniusEquiv R p 1 = frobeniusEquiv R p :=
  RingEquiv.ext (iterateFrobeniusEquiv_one_apply R p)

theorem iterateFrobeniusEquiv_eq_pow : iterateFrobeniusEquiv R p n = frobeniusEquiv R p ^ n :=
  DFunLike.ext' <| show _ = ⇑(RingAut.toPerm _ _) by
    rw [map_pow, Equiv.Perm.coe_pow]; exact (pow_iterate p n).symm

theorem iterateFrobeniusEquiv_symm :
    (iterateFrobeniusEquiv R p n).symm = (frobeniusEquiv R p).symm ^ n := by
  rw [iterateFrobeniusEquiv_eq_pow]; exact (inv_pow _ _).symm

@[simp]
theorem frobeniusEquiv_symm_apply_frobenius (x : R) :
    (frobeniusEquiv R p).symm (frobenius R p x) = x :=
  leftInverse_surjInv PerfectRing.bijective_frobenius x

@[simp]
theorem frobenius_apply_frobeniusEquiv_symm (x : R) :
    frobenius R p ((frobeniusEquiv R p).symm x) = x :=
  surjInv_eq _ _

@[simp]
theorem frobenius_comp_frobeniusEquiv_symm :
    (frobenius R p).comp (frobeniusEquiv R p).symm = RingHom.id R := by
  ext; simp

@[simp]
theorem frobeniusEquiv_symm_comp_frobenius :
    ((frobeniusEquiv R p).symm : R →+* R).comp (frobenius R p) = RingHom.id R := by
  ext; simp

@[simp]
theorem frobeniusEquiv_symm_pow_p (x : R) : ((frobeniusEquiv R p).symm x) ^ p = x :=
  frobenius_apply_frobeniusEquiv_symm R p x

theorem injective_pow_p {x y : R} (h : x ^ p = y ^ p) : x = y := (frobeniusEquiv R p).injective h
#align injective_pow_p injective_pow_p