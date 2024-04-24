def Function.Injective.frame [Sup α] [Inf α] [SupSet α] [InfSet α] [Top α] [Bot α]
    [Frame β] (f : α → β) (hf : Injective f) (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b)
    (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b) (map_sSup : ∀ s, f (sSup s) = ⨆ a ∈ s, f a)
    (map_sInf : ∀ s, f (sInf s) = ⨅ a ∈ s, f a) (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) :
    Frame α where
  __ := hf.completeLattice f map_sup map_inf map_sSup map_sInf map_top map_bot
  inf_sSup_le_iSup_inf a s := by
      change f (a ⊓ sSup s) ≤ f _
      rw [← sSup_image, map_inf, map_sSup s, inf_iSup₂_eq]
      simp_rw [← map_inf]
      exact ((map_sSup _).trans iSup_image).ge
#align function.injective.frame Function.Injective.frame

def Function.Injective.coframe [Sup α] [Inf α] [SupSet α] [InfSet α] [Top α] [Bot α]
    [Coframe β] (f : α → β) (hf : Injective f) (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b)
    (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b) (map_sSup : ∀ s, f (sSup s) = ⨆ a ∈ s, f a)
    (map_sInf : ∀ s, f (sInf s) = ⨅ a ∈ s, f a) (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) :
    Coframe α where
  __ := hf.completeLattice f map_sup map_inf map_sSup map_sInf map_top map_bot
  iInf_sup_le_sup_sInf a s := by
      change f _ ≤ f (a ⊔ sInf s)
      rw [← sInf_image, map_sup, map_sInf s, sup_iInf₂_eq]
      simp_rw [← map_sup]
      exact ((map_sInf _).trans iInf_image).le
#align function.injective.coframe Function.Injective.coframe

def Function.Injective.completeDistribLattice [Sup α] [Inf α] [SupSet α] [InfSet α]
    [Top α] [Bot α] [CompleteDistribLattice β] (f : α → β) (hf : Function.Injective f)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b)
    (map_sSup : ∀ s, f (sSup s) = ⨆ a ∈ s, f a) (map_sInf : ∀ s, f (sInf s) = ⨅ a ∈ s, f a)
    (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) : CompleteDistribLattice α where
  __ := hf.frame f map_sup map_inf map_sSup map_sInf map_top map_bot
  __ := hf.coframe f map_sup map_inf map_sSup map_sInf map_top map_bot
#align function.injective.complete_distrib_lattice Function.Injective.completeDistribLattice

def Function.Injective.completelyDistribLattice [Sup α] [Inf α] [SupSet α] [InfSet α]
    [Top α] [Bot α] [CompletelyDistribLattice β] (f : α → β) (hf : Function.Injective f)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b)
    (map_sSup : ∀ s, f (sSup s) = ⨆ a ∈ s, f a) (map_sInf : ∀ s, f (sInf s) = ⨅ a ∈ s, f a)
    (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) : CompletelyDistribLattice α where
  __ := hf.completeLattice f map_sup map_inf map_sSup map_sInf map_top map_bot
  iInf_iSup_eq g := hf <| by
    simp_rw [iInf, map_sInf, iInf_range, iSup, map_sSup, iSup_range, map_sInf, iInf_range,
      iInf_iSup_eq]

-- See note [reducible non-instances]
/-- Pullback a `CompleteBooleanAlgebra` along an injection. -/
@[reducible]
protected def Function.Injective.completeBooleanAlgebra [Sup α] [Inf α] [SupSet α] [InfSet α]
    [Top α] [Bot α] [HasCompl α] [SDiff α] [CompleteBooleanAlgebra β] (f : α → β)
    (hf : Function.Injective f) (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b)
    (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b) (map_sSup : ∀ s, f (sSup s) = ⨆ a ∈ s, f a)
    (map_sInf : ∀ s, f (sInf s) = ⨅ a ∈ s, f a) (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥)
    (map_compl : ∀ a, f aᶜ = (f a)ᶜ) (map_sdiff : ∀ a b, f (a \ b) = f a \ f b) :
    CompleteBooleanAlgebra α where
  __ := hf.completeDistribLattice f map_sup map_inf map_sSup map_sInf map_top map_bot
  __ := hf.booleanAlgebra f map_sup map_inf map_top map_bot map_compl map_sdiff
#align function.injective.complete_boolean_algebra Function.Injective.completeBooleanAlgebra

def Function.Injective.completeAtomicBooleanAlgebra [Sup α] [Inf α] [SupSet α] [InfSet α]
    [Top α] [Bot α] [HasCompl α] [SDiff α] [CompleteAtomicBooleanAlgebra β] (f : α → β)
    (hf : Function.Injective f) (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b)
    (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b) (map_sSup : ∀ s, f (sSup s) = ⨆ a ∈ s, f a)
    (map_sInf : ∀ s, f (sInf s) = ⨅ a ∈ s, f a) (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥)
    (map_compl : ∀ a, f aᶜ = (f a)ᶜ) (map_sdiff : ∀ a b, f (a \ b) = f a \ f b) :
    CompleteAtomicBooleanAlgebra α where
  __ := hf.completelyDistribLattice f map_sup map_inf map_sSup map_sInf map_top map_bot
  __ := hf.booleanAlgebra f map_sup map_inf map_top map_bot map_compl map_sdiff

end lift

namespace PUnit

variable (s : Set PUnit.{u + 1}) (x y : PUnit.{u + 1})

instance instCompleteAtomicBooleanAlgebra : CompleteAtomicBooleanAlgebra PUnit := by
  refine'
    { PUnit.instBooleanAlgebra with
      sSup := fun _ => unit
      sInf := fun _ => unit
      .. } <;>
  (intros; trivial)

instance instCompleteBooleanAlgebra : CompleteBooleanAlgebra PUnit := inferInstance

instance instCompleteLinearOrder : CompleteLinearOrder PUnit :=
  { PUnit.instCompleteBooleanAlgebra, PUnit.instLinearOrder with }

@[simp]
theorem sSup_eq : sSup s = unit :=
  rfl
#align punit.Sup_eq PUnit.sSup_eq