def toDual : α ≃ αᵒᵈ :=
  Equiv.refl _
#align order_dual.to_dual OrderDual.toDual

def ofDual : αᵒᵈ ≃ α :=
  Equiv.refl _
#align order_dual.of_dual OrderDual.ofDual

def rec {C : αᵒᵈ → Sort*} (h₂ : ∀ a : α, C (toDual a)) : ∀ a : αᵒᵈ, C a :=
  h₂
#align order_dual.rec OrderDual.rec

def Lex (α : Type*) :=
  α
#align lex Lex

def toLex : α ≃ Lex α :=
  Equiv.refl _
#align to_lex toLex

def ofLex : Lex α ≃ α :=
  Equiv.refl _
#align of_lex ofLex

def Lex.rec {β : Lex α → Sort*} (h : ∀ a, β (toLex a)) : ∀ a, β a := fun a => h (ofLex a)
#align lex.rec Lex.rec