def IsBigOWith (c : ℝ) (l : Filter α) (f : α → E) (g : α → F) : Prop :=
  ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖
#align asymptotics.is_O_with Asymptotics.IsBigOWith

def IsBigO (l : Filter α) (f : α → E) (g : α → F) : Prop :=
  ∃ c : ℝ, IsBigOWith c l f g
#align asymptotics.is_O Asymptotics.IsBigO

def IsLittleO (l : Filter α) (f : α → E) (g : α → F) : Prop :=
  ∀ ⦃c : ℝ⦄, 0 < c → IsBigOWith c l f g
#align asymptotics.is_o Asymptotics.IsLittleO

def (h : f =o[l] g) (hc : 0 < c) : ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖ :=
  isLittleO_iff.1 h hc
#align asymptotics.is_o.def Asymptotics.IsLittleO.def

def zero_lt_one

end Defs

/-! ### Conversions -/

def one_pos).mono fun x h₀' => _
      rw [Nat.cast_zero, zero_mul]
      refine' h₀.elim (fun hf => (hf x).trans _) fun hg => hg x
      rwa [one_mul] at h₀'
    · have : (0 : ℝ) < n.succ := Nat.cast_pos.2 n.succ_pos
      exact (isBigOWith_inv this).1 (H.def' <| inv_pos.2 this)
  · refine' fun H => isLittleO_iff.2 fun ε ε0 => _
    rcases exists_nat_gt ε⁻¹ with ⟨n, hn⟩
    have hn₀ : (0 : ℝ) < n := (inv_pos.2 ε0).trans hn
    refine' ((isBigOWith_inv hn₀).2 (H n)).bound.mono fun x hfg => _
    refine' hfg.trans (mul_le_mul_of_nonneg_right (inv_le_of_inv_le ε0 hn.le) _)
    refine' h₀.elim (fun hf => nonneg_of_mul_nonneg_right ((hf x).trans hfg) _) fun h => h x
    exact inv_pos.2 hn₀
#align asymptotics.is_o_iff_nat_mul_le_aux Asymptotics.isLittleO_iff_nat_mul_le_aux