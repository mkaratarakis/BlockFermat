def IsPGroup : Prop :=
  ∀ g : G, ∃ k : ℕ, g ^ p ^ k = 1
#align is_p_group IsPGroup

def powEquiv {n : ℕ} (hn : p.Coprime n) : G ≃ G :=
  let h : ∀ g : G, (Nat.card (Subgroup.zpowers g)).Coprime n := fun g =>
    (Nat.card_zpowers g).symm ▸ hG.orderOf_coprime hn g
  { toFun := (· ^ n)
    invFun := fun g => (powCoprime (h g)).symm ⟨g, Subgroup.mem_zpowers g⟩
    left_inv := fun g =>
      Subtype.ext_iff.1 <|
        (powCoprime (h (g ^ n))).left_inv
          ⟨g, _, Subtype.ext_iff.1 <| (powCoprime (h g)).left_inv ⟨g, Subgroup.mem_zpowers g⟩⟩
    right_inv := fun g =>
      Subtype.ext_iff.1 <| (powCoprime (h g)).right_inv ⟨g, Subgroup.mem_zpowers g⟩ }
#align is_p_group.pow_equiv IsPGroup.powEquiv

def powEquiv' {n : ℕ} (hn : ¬p ∣ n) : G ≃ G :=
  powEquiv hG (hp.out.coprime_iff_not_dvd.mpr hn)
#align is_p_group.pow_equiv' IsPGroup.powEquiv'

def commGroupOfCardEqPrimeSq (hG : card G = p ^ 2) : CommGroup G :=
  @commGroupOfCycleCenterQuotient _ _ _ _ (cyclic_center_quotient_of_card_eq_prime_sq hG) _
    (QuotientGroup.ker_mk' (center G)).le
#align is_p_group.comm_group_of_card_eq_prime_sq IsPGroup.commGroupOfCardEqPrimeSq