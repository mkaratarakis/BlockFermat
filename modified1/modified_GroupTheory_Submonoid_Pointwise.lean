def inv : Inv (Submonoid G) where
  inv S :=
    { carrier := (S : Set G)⁻¹
      mul_mem' := fun ha hb => by rw [mem_inv, mul_inv_rev]; exact mul_mem hb ha
      one_mem' := mem_inv.2 <| by rw [inv_one]; exact S.one_mem' }
#align submonoid.has_inv Submonoid.inv

def involutiveInv : InvolutiveInv (Submonoid G) :=
  SetLike.coe_injective.involutiveInv _ fun _ => rfl

scoped[Pointwise] attribute [instance] Submonoid.involutiveInv AddSubmonoid.involutiveNeg

@[to_additive (attr := simp)]
theorem inv_le_inv (S T : Submonoid G) : S⁻¹ ≤ T⁻¹ ↔ S ≤ T :=
  SetLike.coe_subset_coe.symm.trans Set.inv_subset_inv
#align submonoid.inv_le_inv Submonoid.inv_le_inv

def invOrderIso : Submonoid G ≃o Submonoid G where
  toEquiv := Equiv.inv _
  map_rel_iff' := inv_le_inv _ _
#align submonoid.inv_order_iso Submonoid.invOrderIso

def pointwiseMulAction : MulAction α (Submonoid M) where
  smul a S := S.map (MulDistribMulAction.toMonoidEnd _ M a)
  one_smul S := by
    change S.map _ = S
    simpa only [map_one] using S.map_id
  mul_smul a₁ a₂ S :=
    (congr_arg (fun f : Monoid.End M => S.map f) (MonoidHom.map_mul _ _ _)).trans
      (S.map_map _ _).symm
#align submonoid.pointwise_mul_action Submonoid.pointwiseMulAction

def pointwiseMulAction : MulAction α (AddSubmonoid A) where
  smul a S := S.map (DistribMulAction.toAddMonoidEnd _ A a)
  one_smul S :=
    (congr_arg (fun f : AddMonoid.End A => S.map f) (MonoidHom.map_one _)).trans S.map_id
  mul_smul _ _ S :=
    (congr_arg (fun f : AddMonoid.End A => S.map f) (MonoidHom.map_mul _ _ _)).trans
      (S.map_map _ _).symm
#align add_submonoid.pointwise_mul_action AddSubmonoid.pointwiseMulAction

def one : One (AddSubmonoid R) :=
  ⟨AddMonoidHom.mrange (Nat.castAddMonoidHom R)⟩
scoped[Pointwise] attribute [instance] AddSubmonoid.one

theorem one_eq_mrange : (1 : AddSubmonoid R) = AddMonoidHom.mrange (Nat.castAddMonoidHom R) :=
  rfl
#align add_submonoid.one_eq_mrange AddSubmonoid.one_eq_mrange

def mul : Mul (AddSubmonoid R) :=
  ⟨fun M N => ⨆ s : M, N.map (AddMonoidHom.mul s.1)⟩
scoped[Pointwise] attribute [instance] AddSubmonoid.mul

theorem mul_mem_mul {M N : AddSubmonoid R} {m n : R} (hm : m ∈ M) (hn : n ∈ N) : m * n ∈ M * N :=
  (le_iSup _ ⟨m, hm⟩ : _ ≤ M * N) ⟨n, hn, by rfl⟩
#align add_submonoid.mul_mem_mul AddSubmonoid.mul_mem_mul

def hasDistribNeg : HasDistribNeg (AddSubmonoid R) :=
  { AddSubmonoid.involutiveNeg with
    neg_mul := fun x y => by
      refine'
          le_antisymm (mul_le.2 fun m hm n hn => _)
            ((AddSubmonoid.neg_le _ _).2 <| mul_le.2 fun m hm n hn => _) <;>
        simp only [AddSubmonoid.mem_neg, ← neg_mul] at *
      · exact mul_mem_mul hm hn
      · exact mul_mem_mul (neg_mem_neg.2 hm) hn
    mul_neg := fun x y => by
      refine'
          le_antisymm (mul_le.2 fun m hm n hn => _)
            ((AddSubmonoid.neg_le _ _).2 <| mul_le.2 fun m hm n hn => _) <;>
        simp only [AddSubmonoid.mem_neg, ← mul_neg] at *
      · exact mul_mem_mul hm hn
      · exact mul_mem_mul hm (neg_mem_neg.2 hn) }
#align add_submonoid.has_distrib_neg AddSubmonoid.hasDistribNeg

def mulOneClass : MulOneClass (AddSubmonoid R) where
  one := 1
  mul := (· * ·)
  one_mul M := by rw [one_eq_closure_one_set, ← closure_eq M, closure_mul_closure, one_mul]
  mul_one M := by rw [one_eq_closure_one_set, ← closure_eq M, closure_mul_closure, mul_one]
scoped[Pointwise] attribute [instance] AddSubmonoid.mulOneClass

end NonAssocSemiring

section NonUnitalSemiring

variable [NonUnitalSemiring R]

/-- Semigroup structure on additive submonoids of a (possibly, non-unital) semiring. -/
protected def semigroup : Semigroup (AddSubmonoid R) where
  mul := (· * ·)
  mul_assoc M N P :=
    le_antisymm
      (mul_le.2 fun _mn hmn p hp =>
        suffices M * N ≤ (M * (N * P)).comap (AddMonoidHom.mulRight p) from this hmn
        mul_le.2 fun m hm n hn =>
          show m * n * p ∈ M * (N * P) from
            (mul_assoc m n p).symm ▸ mul_mem_mul hm (mul_mem_mul hn hp))
      (mul_le.2 fun m hm _np hnp =>
        suffices N * P ≤ (M * N * P).comap (AddMonoidHom.mulLeft m) from this hnp
        mul_le.2 fun n hn p hp =>
          show m * (n * p) ∈ M * N * P from mul_assoc m n p ▸ mul_mem_mul (mul_mem_mul hm hn) hp)
scoped[Pointwise] attribute [instance] AddSubmonoid.semigroup
end NonUnitalSemiring

section Semiring

variable [Semiring R]

/-- Monoid structure on additive submonoids of a semiring. -/
protected def monoid : Monoid (AddSubmonoid R) :=
  { AddSubmonoid.semigroup, AddSubmonoid.mulOneClass with }
scoped[Pointwise] attribute [instance] AddSubmonoid.monoid

theorem closure_pow (s : Set R) : ∀ n : ℕ, closure s ^ n = closure (s ^ n)
  | 0 => by rw [pow_zero, pow_zero, one_eq_closure_one_set]
  | n + 1 => by rw [pow_succ, pow_succ, closure_pow s n, closure_mul_closure]
#align add_submonoid.closure_pow AddSubmonoid.closure_pow

structure implied by `Submodule.idemSemiring`.

## Implementation notes

structure of additive submonoids

These definitions are a cut-down versions of the ones around `Submodule.mul`, as that API is
usually more useful. -/

namespace AddSubmonoid

section AddMonoidWithOne

variable [AddMonoidWithOne R]

/-- If `R` is an additive monoid with one (e.g., a semiring), then `1 : AddSubmonoid R` is the range
of `Nat.cast : ℕ → R`. -/
protected def one : One (AddSubmonoid R) :=
  ⟨AddMonoidHom.mrange (Nat.castAddMonoidHom R)⟩
scoped[Pointwise] attribute [instance] AddSubmonoid.one

theorem one_eq_mrange : (1 : AddSubmonoid R) = AddMonoidHom.mrange (Nat.castAddMonoidHom R) :=
  rfl
#align add_submonoid.one_eq_mrange AddSubmonoid.one_eq_mrange

structure on additive submonoids of a (possibly, non-associative) semiring. -/
protected def mulOneClass : MulOneClass (AddSubmonoid R) where
  one := 1
  mul := (· * ·)
  one_mul M := by rw [one_eq_closure_one_set, ← closure_eq M, closure_mul_closure, one_mul]
  mul_one M := by rw [one_eq_closure_one_set, ← closure_eq M, closure_mul_closure, mul_one]
scoped[Pointwise] attribute [instance] AddSubmonoid.mulOneClass

end NonAssocSemiring

section NonUnitalSemiring

variable [NonUnitalSemiring R]

/-- Semigroup structure on additive submonoids of a (possibly, non-unital) semiring. -/
protected def semigroup : Semigroup (AddSubmonoid R) where
  mul := (· * ·)
  mul_assoc M N P :=
    le_antisymm
      (mul_le.2 fun _mn hmn p hp =>
        suffices M * N ≤ (M * (N * P)).comap (AddMonoidHom.mulRight p) from this hmn
        mul_le.2 fun m hm n hn =>
          show m * n * p ∈ M * (N * P) from
            (mul_assoc m n p).symm ▸ mul_mem_mul hm (mul_mem_mul hn hp))
      (mul_le.2 fun m hm _np hnp =>
        suffices N * P ≤ (M * N * P).comap (AddMonoidHom.mulLeft m) from this hnp
        mul_le.2 fun n hn p hp =>
          show m * (n * p) ∈ M * N * P from mul_assoc m n p ▸ mul_mem_mul (mul_mem_mul hm hn) hp)
scoped[Pointwise] attribute [instance] AddSubmonoid.semigroup
end NonUnitalSemiring

section Semiring

variable [Semiring R]

/-- Monoid structure on additive submonoids of a semiring. -/
protected def monoid : Monoid (AddSubmonoid R) :=
  { AddSubmonoid.semigroup, AddSubmonoid.mulOneClass with }
scoped[Pointwise] attribute [instance] AddSubmonoid.monoid

theorem closure_pow (s : Set R) : ∀ n : ℕ, closure s ^ n = closure (s ^ n)
  | 0 => by rw [pow_zero, pow_zero, one_eq_closure_one_set]
  | n + 1 => by rw [pow_succ, pow_succ, closure_pow s n, closure_mul_closure]
#align add_submonoid.closure_pow AddSubmonoid.closure_pow