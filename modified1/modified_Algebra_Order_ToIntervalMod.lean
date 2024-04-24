def toIcoDiv (a b : α) : ℤ :=
  (existsUnique_sub_zsmul_mem_Ico hp b a).choose
#align to_Ico_div toIcoDiv

def toIocDiv (a b : α) : ℤ :=
  (existsUnique_sub_zsmul_mem_Ioc hp b a).choose
#align to_Ioc_div toIocDiv

def toIcoMod (a b : α) : α :=
  b - toIcoDiv hp a b • p
#align to_Ico_mod toIcoMod

def toIocMod (a b : α) : α :=
  b - toIocDiv hp a b • p
#align to_Ioc_mod toIocMod

def QuotientAddGroup.equivIcoMod (a : α) : α ⧸ AddSubgroup.zmultiples p ≃ Set.Ico a (a + p) where
  toFun b :=
    ⟨(toIcoMod_periodic hp a).lift b, QuotientAddGroup.induction_on' b <| toIcoMod_mem_Ico hp a⟩
  invFun := (↑)
  right_inv b := Subtype.ext <| (toIcoMod_eq_self hp).mpr b.prop
  left_inv b := by
    induction b using QuotientAddGroup.induction_on'
    dsimp
    rw [QuotientAddGroup.eq_iff_sub_mem, toIcoMod_sub_self]
    apply AddSubgroup.zsmul_mem_zmultiples
#align quotient_add_group.equiv_Ico_mod QuotientAddGroup.equivIcoMod

def QuotientAddGroup.equivIocMod (a : α) : α ⧸ AddSubgroup.zmultiples p ≃ Set.Ioc a (a + p) where
  toFun b :=
    ⟨(toIocMod_periodic hp a).lift b, QuotientAddGroup.induction_on' b <| toIocMod_mem_Ioc hp a⟩
  invFun := (↑)
  right_inv b := Subtype.ext <| (toIocMod_eq_self hp).mpr b.prop
  left_inv b := by
    induction b using QuotientAddGroup.induction_on'
    dsimp
    rw [QuotientAddGroup.eq_iff_sub_mem, toIocMod_sub_self]
    apply AddSubgroup.zsmul_mem_zmultiples
#align quotient_add_group.equiv_Ioc_mod QuotientAddGroup.equivIocMod

structure on `α ⧸ AddSubgroup.zmultiples p`
-/


section Circular

private theorem toIxxMod_iff (x₁ x₂ x₃ : α) : toIcoMod hp x₁ x₂ ≤ toIocMod hp x₁ x₃ ↔
    toIcoMod hp 0 (x₂ - x₁) + toIcoMod hp 0 (x₁ - x₃) ≤ p := by
  rw [toIcoMod_eq_sub, toIocMod_eq_sub _ x₁, add_le_add_iff_right, ← neg_sub x₁ x₃, toIocMod_neg,
    neg_zero, le_sub_iff_add_le]

private theorem toIxxMod_cyclic_left {x₁ x₂ x₃ : α} (h : toIcoMod hp x₁ x₂ ≤ toIocMod hp x₁ x₃) :
    toIcoMod hp x₂ x₃ ≤ toIocMod hp x₂ x₁ := by
  let x₂' := toIcoMod hp x₁ x₂
  let x₃' := toIcoMod hp x₂' x₃
  have h : x₂' ≤ toIocMod hp x₁ x₃' := by simpa [x₃']
  have h₂₁ : x₂' < x₁ + p := toIcoMod_lt_right _ _ _
  have h₃₂ : x₃' - p < x₂' := sub_lt_iff_lt_add.2 (toIcoMod_lt_right _ _ _)
  suffices hequiv : x₃' ≤ toIocMod hp x₂' x₁ by
    obtain ⟨z, hd⟩ : ∃ z : ℤ, x₂ = x₂' + z • p := ((toIcoMod_eq_iff hp).1 rfl).2
    rw [hd, toIocMod_add_zsmul', toIcoMod_add_zsmul', add_le_add_iff_right]
    assumption -- Porting note: was `simpa`
  rcases le_or_lt x₃' (x₁ + p) with h₃₁ | h₁₃
  · suffices hIoc₂₁ : toIocMod hp x₂' x₁ = x₁ + p from hIoc₂₁.symm.trans_ge h₃₁
    apply (toIocMod_eq_iff hp).2
    exact ⟨⟨h₂₁, by simp [x₂', left_le_toIcoMod]⟩, -1, by simp⟩
  have hIoc₁₃ : toIocMod hp x₁ x₃' = x₃' - p := by
    apply (toIocMod_eq_iff hp).2
    exact ⟨⟨lt_sub_iff_add_lt.2 h₁₃, le_of_lt (h₃₂.trans h₂₁)⟩, 1, by simp⟩
  have not_h₃₂ := (h.trans hIoc₁₃.le).not_lt
  contradiction

private theorem toIxxMod_antisymm (h₁₂₃ : toIcoMod hp a b ≤ toIocMod hp a c)
    (h₁₃₂ : toIcoMod hp a c ≤ toIocMod hp a b) :
    b ≡ a [PMOD p] ∨ c ≡ b [PMOD p] ∨ a ≡ c [PMOD p] := by
  by_contra! h
  rw [modEq_comm] at h
  rw [← (not_modEq_iff_toIcoMod_eq_toIocMod hp).mp h.2.2] at h₁₂₃
  rw [← (not_modEq_iff_toIcoMod_eq_toIocMod hp).mp h.1] at h₁₃₂
  exact h.2.1 ((toIcoMod_inj _).1 <| h₁₃₂.antisymm h₁₂₃)

private theorem toIxxMod_total' (a b c : α) :
    toIcoMod hp b a ≤ toIocMod hp b c ∨ toIcoMod hp b c ≤ toIocMod hp b a := by
  /- an essential ingredient is the lemma saying {a-b} + {b-a} = period if a ≠ b (and = 0 if a = b).
    Thus if a ≠ b and b ≠ c then ({a-b} + {b-c}) + ({c-b} + {b-a}) = 2 * period, so one of
    `{a-b} + {b-c}` and `{c-b} + {b-a}` must be `≤ period` -/
  have := congr_arg₂ (· + ·) (toIcoMod_add_toIocMod_zero hp a b) (toIcoMod_add_toIocMod_zero hp c b)
  simp only [add_add_add_comm] at this -- Porting note (#10691): Was `rw`