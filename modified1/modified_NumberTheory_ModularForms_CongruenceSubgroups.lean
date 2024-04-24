def Gamma (N : ℕ) : Subgroup SL(2, ℤ) :=
  SLMOD(N).ker
#align Gamma Gamma

def Gamma0 (N : ℕ) : Subgroup SL(2, ℤ) where
  carrier := { g : SL(2, ℤ) | ((↑ₘg 1 0 : ℤ) : ZMod N) = 0 }
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq]
    have h := (Matrix.two_mul_expl a.1 b.1).2.2.1
    simp only [coe_matrix_coe, coe_mul, Int.coe_castRingHom, map_apply, Set.mem_setOf_eq] at *
    rw [h]
    simp [ha, hb]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq]
    rw [SL2_inv_expl a]
    simp only [cons_val_zero, cons_val_one, head_cons, coe_matrix_coe,
      coe_mk, Int.coe_castRingHom, map_apply, Int.cast_neg, neg_eq_zero, Set.mem_setOf_eq] at *
    exact ha
#align Gamma0 Gamma0

def Gamma0Map (N : ℕ) : Gamma0 N →* ZMod N where
  toFun g := ((↑ₘg 1 1 : ℤ) : ZMod N)
  map_one' := by simp
  map_mul' := by
    intro A B
    have := (two_mul_expl A.1.1 B.1.1).2.2.2
    simp only [Subgroup.coe_mul, coe_matrix_coe, coe_mul, Int.coe_castRingHom, map_apply] at *
    rw [this]
    have ha := A.property
    simp only [Int.cast_add, Int.cast_mul, add_left_eq_self, Gamma0_mem,
      coe_matrix_coe, Int.coe_castRingHom, map_apply] at *
    rw [ha]
    simp
#align Gamma_0_map Gamma0Map

def Gamma1' (N : ℕ) : Subgroup (Gamma0 N) :=
  (Gamma0Map N).ker
#align Gamma1' Gamma1'

def Gamma1 (N : ℕ) : Subgroup SL(2, ℤ) :=
  Subgroup.map ((Gamma0 N).subtype.comp (Gamma1' N).subtype) ⊤
#align Gamma1 Gamma1

def IsCongruenceSubgroup (Γ : Subgroup SL(2, ℤ)) : Prop :=
  ∃ N : ℕ+, Gamma N ≤ Γ
#align is_congruence_subgroup IsCongruenceSubgroup