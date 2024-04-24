def CauchyFilter (α : Type u) [UniformSpace α] : Type u :=
  { f : Filter α // Cauchy f }
set_option linter.uppercaseLean3 false in
#align Cauchy CauchyFilter

def gen (s : Set (α × α)) : Set (CauchyFilter α × CauchyFilter α) :=
  { p | s ∈ p.1.val ×ˢ p.2.val }
set_option linter.uppercaseLean3 false in
#align Cauchy.gen CauchyFilter.gen

def pureCauchy (a : α) : CauchyFilter α :=
  ⟨pure a, cauchy_pure⟩
set_option linter.uppercaseLean3 false in
#align Cauchy.pure_cauchy CauchyFilter.pureCauchy

def extend (f : α → β) : CauchyFilter α → β :=
  if UniformContinuous f then denseInducing_pureCauchy.extend f
  else fun x => f (nonempty_cauchyFilter_iff.1 ⟨x⟩).some
set_option linter.uppercaseLean3 false in
#align Cauchy.extend CauchyFilter.extend

def Completion := SeparationQuotient (CauchyFilter α)
#align uniform_space.completion UniformSpace.Completion

def coe' : α → Completion α := SeparationQuotient.mk ∘ pureCauchy

/-- Automatic coercion from `α` to its completion. Not always injective. -/
instance : Coe α (Completion α) :=
  ⟨coe' α⟩

-- note [use has_coe_t]
protected theorem coe_eq : ((↑) : α → Completion α) = SeparationQuotient.mk ∘ pureCauchy := rfl
#align uniform_space.completion.coe_eq UniformSpace.Completion.coe_eq

def cPkg {α : Type*} [UniformSpace α] : AbstractCompletion α where
  space := Completion α
  coe := (↑)
  uniformStruct := by infer_instance
  complete := by infer_instance
  separation := by infer_instance
  uniformInducing := Completion.uniformInducing_coe α
  dense := Completion.denseRange_coe
#align uniform_space.completion.cpkg UniformSpace.Completion.cPkg

def UniformCompletion.completeEquivSelf [CompleteSpace α] [T0Space α] : Completion α ≃ᵤ α :=
  AbstractCompletion.compareEquiv Completion.cPkg AbstractCompletion.ofComplete
#align uniform_space.completion.uniform_completion.complete_equiv_self UniformSpace.Completion.UniformCompletion.completeEquivSelf

def extension (f : α → β) : Completion α → β :=
  cPkg.extend f
#align uniform_space.completion.extension UniformSpace.Completion.extension

def map (f : α → β) : Completion α → Completion β :=
  cPkg.map cPkg f
#align uniform_space.completion.map UniformSpace.Completion.map

def completionSeparationQuotientEquiv (α : Type u) [UniformSpace α] :
    Completion (SeparationQuotient α) ≃ Completion α := by
  refine ⟨Completion.extension (lift' ((↑) : α → Completion α)),
    Completion.map SeparationQuotient.mk, fun a ↦ ?_, fun a ↦ ?_⟩
  · refine induction_on a (isClosed_eq (continuous_map.comp continuous_extension) continuous_id) ?_
    refine SeparationQuotient.surjective_mk.forall.2 fun a ↦ ?_
    rw [extension_coe (uniformContinuous_lift' _), lift'_mk (uniformContinuous_coe α),
      map_coe uniformContinuous_mk]
  · refine induction_on a
      (isClosed_eq (continuous_extension.comp continuous_map) continuous_id) fun a ↦ ?_
    rw [map_coe uniformContinuous_mk, extension_coe (uniformContinuous_lift' _),
      lift'_mk (uniformContinuous_coe _)]
#align uniform_space.completion.completion_separation_quotient_equiv UniformSpace.Completion.completionSeparationQuotientEquiv

def extension₂ (f : α → β → γ) : Completion α → Completion β → γ :=
  cPkg.extend₂ cPkg f
#align uniform_space.completion.extension₂ UniformSpace.Completion.extension₂

def map₂ (f : α → β → γ) : Completion α → Completion β → Completion γ :=
  cPkg.map₂ cPkg cPkg f
#align uniform_space.completion.map₂ UniformSpace.Completion.map₂