def SlashInvariantForm.copy (f : SlashInvariantForm Γ k) (f' : ℍ → ℂ) (h : f' = ⇑f) :
    SlashInvariantForm Γ k where
  toFun := f'
  slash_action_eq' := h.symm ▸ f.slash_action_eq'
#align slash_invariant_form.copy SlashInvariantForm.copy

def coeHom : SlashInvariantForm Γ k →+ ℍ → ℂ where
  toFun f := f
  map_zero' := rfl
  map_add' _ _ := rfl
#align slash_invariant_form.coe_hom SlashInvariantForm.coeHom

def const (x : ℂ) : SlashInvariantForm Γ 0 where
  toFun := Function.const _ x
  slash_action_eq' A := ModularForm.is_invariant_const A x

instance : One (SlashInvariantForm Γ 0) where
  one := { const 1 with toFun := 1 }

@[simp]
theorem one_coe_eq_one : ((1 : SlashInvariantForm Γ 0) : ℍ → ℂ) = 1 :=
  rfl
#align slash_invariant_form.one_coe_eq_one SlashInvariantForm.one_coe_eq_one

structure SlashInvariantForm where
  toFun : ℍ → ℂ
  slash_action_eq' : ∀ γ : Γ, toFun ∣[k] γ = toFun
#align slash_invariant_form SlashInvariantForm