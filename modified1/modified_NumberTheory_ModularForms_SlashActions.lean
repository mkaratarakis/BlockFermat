def monoidHomSlashAction {β G H α γ : Type*} [Group G] [AddMonoid α] [SMul γ α] [Group H]
    [SlashAction β G α γ] (h : H →* G) : SlashAction β H α γ where
  map k g := SlashAction.map γ k (h g)
  zero_slash k g := SlashAction.zero_slash k (h g)
  slash_one k a := by simp only [map_one, SlashAction.slash_one]
  slash_mul k g gg a := by simp only [map_mul, SlashAction.slash_mul]
  smul_slash _ _ := SlashAction.smul_slash _ _
  add_slash _ g _ _ := SlashAction.add_slash _ (h g) _ _
#align monoid_hom_slash_action monoidHomSlashAction

def slash (k : ℤ) (γ : GL(2, ℝ)⁺) (f : ℍ → ℂ) (x : ℍ) : ℂ :=
  f (γ • x) * (((↑ₘγ).det : ℝ) : ℂ) ^ (k - 1) * UpperHalfPlane.denom γ x ^ (-k)
#align modular_form.slash ModularForm.slash

def (A : GL(2, ℝ)⁺) : f ∣[k] A = slash k A f :=
  rfl
#align modular_form.slash_def ModularForm.slash_def