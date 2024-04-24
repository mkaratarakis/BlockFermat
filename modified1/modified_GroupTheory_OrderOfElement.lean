def IsOfFinOrder (x : G) : Prop :=
  (1 : G) ∈ periodicPts (x * ·)
#align is_of_fin_order IsOfFinOrder

def orderOf (x : G) : ℕ :=
  minimalPeriod (x * ·) 1
#align order_of orderOf

def IsOfFinOrder.unit {M} [Monoid M] {x : M} (hx : IsOfFinOrder x) : Mˣ :=
⟨x, x ^ (orderOf x - 1),
  by rw [← _root_.pow_succ', tsub_add_cancel_of_le (by exact hx.orderOf_pos), pow_orderOf_eq_one],
  by rw [← _root_.pow_succ, tsub_add_cancel_of_le (by exact hx.orderOf_pos), pow_orderOf_eq_one]⟩

lemma IsOfFinOrder.isUnit {M} [Monoid M] {x : M} (hx : IsOfFinOrder x) : IsUnit x := ⟨hx.unit, rfl⟩

variable (x)

@[to_additive]
theorem orderOf_pow' (h : n ≠ 0) : orderOf (x ^ n) = orderOf x / gcd (orderOf x) n := by
  unfold orderOf
  rw [← minimalPeriod_iterate_eq_div_gcd h, mul_left_iterate]
#align order_of_pow' orderOf_pow'

def finEquivPowers (x : G) (hx : IsOfFinOrder x) : Fin (orderOf x) ≃ powers x :=
  Equiv.ofBijective (fun n ↦ ⟨x ^ (n : ℕ), ⟨n, rfl⟩⟩) ⟨fun ⟨_, h₁⟩ ⟨_, h₂⟩ ij ↦
    Fin.ext (pow_injOn_Iio_orderOf h₁ h₂ (Subtype.mk_eq_mk.1 ij)), fun ⟨_, i, rfl⟩ ↦
      ⟨⟨i % orderOf x, mod_lt _ hx.orderOf_pos⟩, Subtype.eq <| pow_mod_orderOf _ _⟩⟩
#align fin_equiv_powers finEquivPowers

def finEquivZPowers (x : G) (hx : IsOfFinOrder x) :
    Fin (orderOf x) ≃ (zpowers x : Set G) :=
  (finEquivPowers x hx).trans <| Equiv.Set.ofEq hx.powers_eq_zpowers
#align fin_equiv_zpowers finEquivZPowers

def powersEquivPowers (h : orderOf x = orderOf y) : powers x ≃ powers y :=
  (finEquivPowers x <| isOfFinOrder_of_finite _).symm.trans <|
    (Fin.castIso h).toEquiv.trans <| finEquivPowers y <| isOfFinOrder_of_finite _
#align powers_equiv_powers powersEquivPowers

def zpowersEquivZPowers (h : orderOf x = orderOf y) :
    (Subgroup.zpowers x : Set G) ≃ (Subgroup.zpowers y : Set G) :=
  (finEquivZPowers x <| isOfFinOrder_of_finite _).symm.trans <| (Fin.castIso h).toEquiv.trans <|
    finEquivZPowers y <| isOfFinOrder_of_finite _
#align zpowers_equiv_zpowers zpowersEquivZPowers

def powCoprime {G : Type*} [Group G] (h : (Nat.card G).Coprime n) : G ≃ G
    where
  toFun g := g ^ n
  invFun g := g ^ (Nat.card G).gcdB n
  left_inv g := by
    have key := congr_arg (g ^ ·) ((Nat.card G).gcd_eq_gcd_ab n)
    dsimp only at key
    rwa [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, zpow_natCast, h.gcd_eq_one,
      pow_one, pow_card_eq_one', one_zpow, one_mul, eq_comm] at key
  right_inv g := by
    have key := congr_arg (g ^ ·) ((Nat.card G).gcd_eq_gcd_ab n)
    dsimp only at key
    rwa [zpow_add, zpow_mul, zpow_mul', zpow_natCast, zpow_natCast, zpow_natCast, h.gcd_eq_one,
      pow_one, pow_card_eq_one', one_zpow, one_mul, eq_comm] at key
#align pow_coprime powCoprime

def submonoidOfIdempotent {M : Type*} [LeftCancelMonoid M] [Finite M] (S : Set M)
    (hS1 : S.Nonempty) (hS2 : S * S = S) : Submonoid M :=
  have pow_mem : ∀ a : M, a ∈ S → ∀ n : ℕ, a ^ (n + 1) ∈ S := fun a ha =>
    Nat.rec (by rwa [Nat.zero_eq, zero_add, pow_one]) fun n ih =>
      (congr_arg₂ (· ∈ ·) (pow_succ a (n + 1)).symm hS2).mp (Set.mul_mem_mul ih ha)
  { carrier := S
    one_mem' := by
      obtain ⟨a, ha⟩ := hS1
      rw [← pow_orderOf_eq_one a, ← tsub_add_cancel_of_le (succ_le_of_lt (orderOf_pos a))]
      exact pow_mem a ha (orderOf a - 1)
    mul_mem' := fun ha hb => (congr_arg₂ (· ∈ ·) rfl hS2).mp (Set.mul_mem_mul ha hb) }
#align submonoid_of_idempotent submonoidOfIdempotent

def subgroupOfIdempotent {G : Type*} [Group G] [Finite G] (S : Set G) (hS1 : S.Nonempty)
    (hS2 : S * S = S) : Subgroup G :=
  { submonoidOfIdempotent S hS1 hS2 with
    carrier := S
    inv_mem' := fun {a} ha => show a⁻¹ ∈ submonoidOfIdempotent S hS1 hS2 by
      rw [← one_mul a⁻¹, ← pow_one a, ← pow_orderOf_eq_one a, ← pow_sub a (orderOf_pos a)]
      exact pow_mem ha (orderOf a - 1) }
#align subgroup_of_idempotent subgroupOfIdempotent

def powCardSubgroup {G : Type*} [Group G] [Fintype G] (S : Set G) (hS : S.Nonempty) : Subgroup G :=
  have one_mem : (1 : G) ∈ S ^ Fintype.card G := by
    obtain ⟨a, ha⟩ := hS
    rw [← pow_card_eq_one]
    exact Set.pow_mem_pow ha (Fintype.card G)
  subgroupOfIdempotent (S ^ Fintype.card G) ⟨1, one_mem⟩ <| by
    classical
    apply (Set.eq_of_subset_of_card_le (Set.subset_mul_left _ one_mem) (ge_of_eq _)).symm
    simp_rw [← pow_add,
        Group.card_pow_eq_card_pow_card_univ S (Fintype.card G + Fintype.card G) le_add_self]
#align pow_card_subgroup powCardSubgroup