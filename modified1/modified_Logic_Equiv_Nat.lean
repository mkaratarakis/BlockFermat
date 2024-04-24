def boolProdNatEquivNat : Bool × ℕ ≃ ℕ where
  toFun := uncurry bit
  invFun := boddDiv2
  left_inv := fun ⟨b, n⟩ => by simp only [bodd_bit, div2_bit, uncurry_apply_pair, boddDiv2_eq]
  right_inv n := by simp only [bit_decomp, boddDiv2_eq, uncurry_apply_pair]
#align equiv.bool_prod_nat_equiv_nat Equiv.boolProdNatEquivNat

def natSumNatEquivNat : ℕ ⊕ ℕ ≃ ℕ :=
  (boolProdEquivSum ℕ).symm.trans boolProdNatEquivNat
#align equiv.nat_sum_nat_equiv_nat Equiv.natSumNatEquivNat

def intEquivNat : ℤ ≃ ℕ :=
  intEquivNatSumNat.trans natSumNatEquivNat
#align equiv.int_equiv_nat Equiv.intEquivNat

def prodEquivOfEquivNat (e : α ≃ ℕ) : α × α ≃ α :=
  calc
    α × α ≃ ℕ × ℕ := prodCongr e e
    _ ≃ ℕ := pairEquiv
    _ ≃ α := e.symm
#align equiv.prod_equiv_of_equiv_nat Equiv.prodEquivOfEquivNat