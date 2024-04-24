def Shrink (α : Type v) [Small.{w} α] : Type w :=
  Classical.choose (@Small.equiv_small α _)
#align shrink Shrink

def equivShrink (α : Type v) [Small.{w} α] : α ≃ Shrink α :=
  Nonempty.some (Classical.choose_spec (@Small.equiv_small α _))
#align equiv_shrink equivShrink

def Shrink.rec [Small.{w} α] {F : Shrink α → Sort v}
    (h : ∀ X, F (equivShrink _ X)) : ∀ X, F X :=
  fun X => ((equivShrink _).apply_symm_apply X) ▸ (h _)

-- Porting note: Priority changed to 101
instance (priority := 101) small_self (α : Type v) : Small.{v} α :=
  Small.mk' <| Equiv.refl α
#align small_self small_self