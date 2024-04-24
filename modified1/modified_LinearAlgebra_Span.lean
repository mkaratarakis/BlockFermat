def span (s : Set M) : Submodule R M :=
  sInf { p | s ⊆ p }
#align submodule.span Submodule.span

def gi : GaloisInsertion (@span R M _ _ _) (↑)
    where
  choice s _ := span R s
  gc _ _ := span_le
  le_l_u _ := subset_span
  choice_eq _ _ := rfl
#align submodule.gi Submodule.gi

def prod : Submodule R (M × M') :=
  { p.toAddSubmonoid.prod q₁.toAddSubmonoid with
    carrier := p ×ˢ q₁
    smul_mem' := by rintro a ⟨x, y⟩ ⟨hx, hy⟩; exact ⟨smul_mem _ a hx, smul_mem _ a hy⟩ }
#align submodule.prod Submodule.prod

def toSpanSingleton (x : M) : R →ₗ[R] M :=
  LinearMap.id.smulRight x
#align linear_map.to_span_singleton LinearMap.toSpanSingleton

def toSpanNonzeroSingleton : R ≃ₗ[R] R ∙ x :=
  LinearEquiv.trans
    (LinearEquiv.ofInjective (LinearMap.toSpanSingleton R M x)
      (ker_eq_bot.1 <| ker_toSpanSingleton R M h))
    (LinearEquiv.ofEq (range <| toSpanSingleton R M x) (R ∙ x) (span_singleton_eq_range R M x).symm)
#align linear_equiv.to_span_nonzero_singleton LinearEquiv.toSpanNonzeroSingleton