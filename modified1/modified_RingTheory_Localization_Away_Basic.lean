def invSelf : S :=
  mk' S (1 : R) ⟨x, Submonoid.mem_powers _⟩
#align is_localization.away.inv_self IsLocalization.Away.invSelf

def lift (hg : IsUnit (g x)) : S →+* P :=
  IsLocalization.lift fun y : Submonoid.powers x =>
    show IsUnit (g y.1) by
      obtain ⟨n, hn⟩ := y.2
      rw [← hn, g.map_pow]
      exact IsUnit.map (powMonoidHom n : P →* P) hg
#align is_localization.away.lift IsLocalization.Away.lift

def awayToAwayRight (y : R) [Algebra R P] [IsLocalization.Away (x * y) P] : S →+* P :=
  lift x <|
    show IsUnit ((algebraMap R P) x) from
      isUnit_of_mul_eq_one ((algebraMap R P) x) (mk' P y ⟨x * y, Submonoid.mem_powers _⟩) <| by
        rw [mul_mk'_eq_mk'_of_mul, mk'_self]
#align is_localization.away.away_to_away_right IsLocalization.Away.awayToAwayRight

def map (f : R →+* P) (r : R) [IsLocalization.Away r S]
    [IsLocalization.Away (f r) Q] : S →+* Q :=
  IsLocalization.map Q f
    (show Submonoid.powers r ≤ (Submonoid.powers (f r)).comap f by
      rintro x ⟨n, rfl⟩
      use n
      simp)
#align is_localization.away.map IsLocalization.Away.map

def atUnit (x : R) (e : IsUnit x) [IsLocalization.Away x S] : R ≃ₐ[R] S :=
  atUnits R (Submonoid.powers x)
    (by rwa [Submonoid.powers_eq_closure, Submonoid.closure_le, Set.singleton_subset_iff])
#align is_localization.at_unit IsLocalization.atUnit

def atOne [IsLocalization.Away (1 : R) S] : R ≃ₐ[R] S :=
  @atUnit R _ S _ _ (1 : R) isUnit_one _
#align is_localization.at_one IsLocalization.atOne

def selfZPow (m : ℤ) : B :=
  if _ : 0 ≤ m then algebraMap _ _ x ^ m.natAbs else mk' _ (1 : R) (Submonoid.pow x m.natAbs)
#align self_zpow selfZPow