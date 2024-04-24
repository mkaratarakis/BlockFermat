def IsTorsion :=
  ∀ g : G, IsOfFinOrder g
#align monoid.is_torsion Monoid.IsTorsion

def IsTorsion.group [Monoid G] (tG : IsTorsion G) : Group G :=
  { ‹Monoid G› with
    inv := fun g => g ^ (orderOf g - 1)
    mul_left_inv := fun g => by
      erw [← pow_succ, tsub_add_cancel_of_le, pow_orderOf_eq_one]
      exact (tG g).orderOf_pos }
#align is_torsion.group IsTorsion.group

def torsion : Submonoid G where
  carrier := { x | IsOfFinOrder x }
  one_mem' := isOfFinOrder_one
  mul_mem' hx hy := hx.mul hy
#align comm_monoid.torsion CommMonoid.torsion

def primaryComponent : Submonoid G where
  carrier := { g | ∃ n : ℕ, orderOf g = p ^ n }
  one_mem' := ⟨0, by rw [pow_zero, orderOf_one]⟩
  mul_mem' hg₁ hg₂ :=
    exists_orderOf_eq_prime_pow_iff.mpr <| by
      obtain ⟨m, hm⟩ := exists_orderOf_eq_prime_pow_iff.mp hg₁
      obtain ⟨n, hn⟩ := exists_orderOf_eq_prime_pow_iff.mp hg₂
      exact
        ⟨m + n, by
          rw [mul_pow, pow_add, pow_mul, hm, one_pow, Monoid.one_mul, mul_comm, pow_mul, hn,
            one_pow]⟩
#align comm_monoid.primary_component CommMonoid.primaryComponent

def torsionMulEquiv (tG : IsTorsion G) : torsion G ≃* G :=
  (MulEquiv.submonoidCongr tG.torsion_eq_top).trans Submonoid.topEquiv
#align monoid.is_torsion.torsion_mul_equiv Monoid.IsTorsion.torsionMulEquiv

def Torsion.ofTorsion : torsion (torsion G) ≃* torsion G :=
  Monoid.IsTorsion.torsionMulEquiv CommMonoid.torsion.isTorsion
#align torsion.of_torsion Torsion.ofTorsion

def torsion : Subgroup G :=
  { CommMonoid.torsion G with inv_mem' := fun hx => IsOfFinOrder.inv hx }
#align comm_group.torsion CommGroup.torsion

def primaryComponent : Subgroup G :=
  { CommMonoid.primaryComponent G p with
    inv_mem' := fun {g} ⟨n, hn⟩ => ⟨n, (orderOf_inv g).trans hn⟩ }
#align comm_group.primary_component CommGroup.primaryComponent

def IsTorsionFree :=
  ∀ g : G, g ≠ 1 → ¬IsOfFinOrder g
#align monoid.is_torsion_free Monoid.IsTorsionFree