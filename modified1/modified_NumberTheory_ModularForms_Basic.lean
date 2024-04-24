def ModularForm.copy (f : ModularForm Γ k) (f' : ℍ → ℂ) (h : f' = ⇑f) :
    ModularForm Γ k where
  toSlashInvariantForm := f.1.copy f' h
  holo' := h.symm ▸ f.holo'
  bdd_at_infty' A := h.symm ▸ f.bdd_at_infty' A
#align modular_form.copy ModularForm.copy

def CuspForm.copy (f : CuspForm Γ k) (f' : ℍ → ℂ) (h : f' = ⇑f) : CuspForm Γ k where
  toSlashInvariantForm := f.1.copy f' h
  holo' := h.symm ▸ f.holo'
  zero_at_infty' A := h.symm ▸ f.zero_at_infty' A
#align cusp_form.copy CuspForm.copy

def coeHom : ModularForm Γ k →+ ℍ → ℂ where
  toFun f := f
  map_zero' := coe_zero
  map_add' _ _ := rfl
#align modular_form.coe_hom ModularForm.coeHom

def mul {k_1 k_2 : ℤ} {Γ : Subgroup SL(2, ℤ)} (f : ModularForm Γ k_1) (g : ModularForm Γ k_2) :
    ModularForm Γ (k_1 + k_2) where
  toSlashInvariantForm := f.1.mul g.1
  holo' := f.holo'.mul g.holo'
  bdd_at_infty' A := by
    -- Porting note: was `by simpa using ...`
    -- `mul_slash_SL2` is no longer a `simp` and `simpa only [mul_slash_SL2] using ...` failed
    rw [SlashInvariantForm.coe_mul, mul_slash_SL2]
    exact (f.bdd_at_infty' A).mul (g.bdd_at_infty' A)
#align modular_form.mul ModularForm.mul

def const (x : ℂ) : ModularForm Γ 0 where
  toSlashInvariantForm := .const x
  holo' x := mdifferentiableAt_const 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
  bdd_at_infty' A := by
    simpa only [SlashInvariantForm.const_toFun,
      ModularForm.is_invariant_const] using atImInfty.const_boundedAtFilter x

instance : One (ModularForm Γ 0) where
  one := { const 1 with toSlashInvariantForm := 1 }

@[simp]
theorem one_coe_eq_one : ⇑(1 : ModularForm Γ 0) = 1 :=
  rfl
#align modular_form.one_coe_eq_one ModularForm.one_coe_eq_one

def coeHom : CuspForm Γ k →+ ℍ → ℂ where
  toFun f := f
  map_zero' := CuspForm.coe_zero
  map_add' _ _ := rfl
#align cusp_form.coe_hom CuspForm.coeHom

structure ModularForm extends SlashInvariantForm Γ k where
  holo' : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (toSlashInvariantForm : ℍ → ℂ)
  bdd_at_infty' : ∀ A : SL(2, ℤ), IsBoundedAtImInfty (toSlashInvariantForm ∣[k] A)
#align modular_form ModularForm

structure CuspForm extends SlashInvariantForm Γ k where
  holo' : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (toSlashInvariantForm : ℍ → ℂ)
  zero_at_infty' : ∀ A : SL(2, ℤ), IsZeroAtImInfty (toSlashInvariantForm ∣[k] A)
#align cusp_form CuspForm