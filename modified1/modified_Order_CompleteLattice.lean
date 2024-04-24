def completeLatticeOfInf (α : Type*) [H1 : PartialOrder α] [H2 : InfSet α]
    (isGLB_sInf : ∀ s : Set α, IsGLB s (sInf s)) : CompleteLattice α where
  __ := H1; __ := H2
  bot := sInf univ
  bot_le x := (isGLB_sInf univ).1 trivial
  top := sInf ∅
  le_top a := (isGLB_sInf ∅).2 <| by simp
  sup a b := sInf { x : α | a ≤ x ∧ b ≤ x }
  inf a b := sInf {a, b}
  le_inf a b c hab hac := by
    apply (isGLB_sInf _).2
    simp [*]
  inf_le_right a b := (isGLB_sInf _).1 <| mem_insert_of_mem _ <| mem_singleton _
  inf_le_left a b := (isGLB_sInf _).1 <| mem_insert _ _
  sup_le a b c hac hbc := (isGLB_sInf _).1 <| by simp [*]
  le_sup_left a b := (isGLB_sInf _).2 fun x => And.left
  le_sup_right a b := (isGLB_sInf _).2 fun x => And.right
  le_sInf s a ha := (isGLB_sInf s).2 ha
  sInf_le s a ha := (isGLB_sInf s).1 ha
  sSup s := sInf (upperBounds s)
  le_sSup s a ha := (isGLB_sInf (upperBounds s)).2 fun b hb => hb ha
  sSup_le s a ha := (isGLB_sInf (upperBounds s)).1 ha
#align complete_lattice_of_Inf completeLatticeOfInf

def completeLatticeOfCompleteSemilatticeInf (α : Type*) [CompleteSemilatticeInf α] :
    CompleteLattice α :=
  completeLatticeOfInf α fun s => isGLB_sInf s
#align complete_lattice_of_complete_semilattice_Inf completeLatticeOfCompleteSemilatticeInf

def completeLatticeOfSup (α : Type*) [H1 : PartialOrder α] [H2 : SupSet α]
    (isLUB_sSup : ∀ s : Set α, IsLUB s (sSup s)) : CompleteLattice α where
  __ := H1; __ := H2
  top := sSup univ
  le_top x := (isLUB_sSup univ).1 trivial
  bot := sSup ∅
  bot_le x := (isLUB_sSup ∅).2 <| by simp
  sup a b := sSup {a, b}
  sup_le a b c hac hbc := (isLUB_sSup _).2 (by simp [*])
  le_sup_left a b := (isLUB_sSup _).1 <| mem_insert _ _
  le_sup_right a b := (isLUB_sSup _).1 <| mem_insert_of_mem _ <| mem_singleton _
  inf a b := sSup { x | x ≤ a ∧ x ≤ b }
  le_inf a b c hab hac := (isLUB_sSup _).1 <| by simp [*]
  inf_le_left a b := (isLUB_sSup _).2 fun x => And.left
  inf_le_right a b := (isLUB_sSup _).2 fun x => And.right
  sInf s := sSup (lowerBounds s)
  sSup_le s a ha := (isLUB_sSup s).2 ha
  le_sSup s a ha := (isLUB_sSup s).1 ha
  sInf_le s a ha := (isLUB_sSup (lowerBounds s)).2 fun b hb => hb ha
  le_sInf s a ha := (isLUB_sSup (lowerBounds s)).1 ha
#align complete_lattice_of_Sup completeLatticeOfSup

def completeLatticeOfCompleteSemilatticeSup (α : Type*) [CompleteSemilatticeSup α] :
    CompleteLattice α :=
  completeLatticeOfSup α fun s => isLUB_sSup s
#align complete_lattice_of_complete_semilattice_Sup completeLatticeOfCompleteSemilatticeSup

def a b := by
    split_ifs with h
    · simp [h]
    · simp [(CompleteLinearOrder.le_total a b).resolve_left h]
  max_def a b := by
    split_ifs with h
    · simp [h]
    · simp [(CompleteLinearOrder.le_total a b).resolve_left h]

namespace OrderDual

variable (α)

instance instCompleteLattice [CompleteLattice α] : CompleteLattice αᵒᵈ where
  __ := OrderDual.instLattice α
  __ := OrderDual.supSet α
  __ := OrderDual.infSet α
  __ := OrderDual.instBoundedOrder α
  le_sSup := @CompleteLattice.sInf_le α _
  sSup_le := @CompleteLattice.le_sInf α _
  sInf_le := @CompleteLattice.le_sSup α _
  le_sInf := @CompleteLattice.sSup_le α _

instance [CompleteLinearOrder α] : CompleteLinearOrder αᵒᵈ where
  __ := OrderDual.instCompleteLattice α
  __ := OrderDual.instLinearOrder α

end OrderDual

open OrderDual

section

variable [CompleteLattice α] {s t : Set α} {a b : α}

@[simp]
theorem toDual_sSup (s : Set α) : toDual (sSup s) = sInf (ofDual ⁻¹' s) :=
  rfl
#align to_dual_Sup toDual_sSup

def Function.Injective.completeLattice [Sup α] [Inf α] [SupSet α] [InfSet α] [Top α]
    [Bot α] [CompleteLattice β] (f : α → β) (hf : Function.Injective f)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b)
    (map_sSup : ∀ s, f (sSup s) = ⨆ a ∈ s, f a) (map_sInf : ∀ s, f (sInf s) = ⨅ a ∈ s, f a)
    (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) : CompleteLattice α where
  -- we cannot use BoundedOrder.lift here as the `LE` instance doesn't exist yet
  __ := hf.lattice f map_sup map_inf
  le_sSup _ a h := (le_iSup₂ a h).trans (map_sSup _).ge
  sSup_le _ _ h := (map_sSup _).trans_le <| iSup₂_le h
  sInf_le _ a h := (map_sInf _).trans_le <| iInf₂_le a h
  le_sInf _ _ h := (le_iInf₂ h).trans (map_sInf _).ge
  top := ⊤
  le_top _ := (@le_top β _ _ _).trans map_top.ge
  bot := ⊥
  bot_le _ := map_bot.le.trans bot_le
#align function.injective.complete_lattice Function.Injective.completeLattice

structure is complete. -/
class CompleteLinearOrder (α : Type*) extends CompleteLattice α where
  /-- A linear order is total. -/
  le_total (a b : α) : a ≤ b ∨ b ≤ a
  /-- In a linearly ordered type, we assume the order relations are all decidable. -/
  decidableLE : DecidableRel (· ≤ · : α → α → Prop)
  /-- In a linearly ordered type, we assume the order relations are all decidable. -/
  decidableEq : DecidableEq α := @decidableEqOfDecidableLE _ _ decidableLE
  /-- In a linearly ordered type, we assume the order relations are all decidable. -/
  decidableLT : DecidableRel (· < · : α → α → Prop) :=
    @decidableLTOfDecidableLE _ _ decidableLE
#align complete_linear_order CompleteLinearOrder