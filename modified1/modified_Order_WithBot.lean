def WithBot (α : Type*) :=
  Option α
#align with_bot WithBot

def some : α → WithBot α :=
  Option.some

-- Porting note: changed this from `CoeTC` to `Coe` but I am not 100% confident that's correct.
instance coe : Coe α (WithBot α) :=
  ⟨some⟩

instance bot : Bot (WithBot α) :=
  ⟨none⟩

instance inhabited : Inhabited (WithBot α) :=
  ⟨⊥⟩

instance nontrivial [Nonempty α] : Nontrivial (WithBot α) :=
  Option.nontrivial

open Function

theorem coe_injective : Injective ((↑) : α → WithBot α) :=
  Option.some_injective _
#align with_bot.coe_injective WithBot.coe_injective

def recBotCoe {C : WithBot α → Sort*} (bot : C ⊥) (coe : ∀ a : α, C a) : ∀ n : WithBot α, C n
  | ⊥ => bot
  | (a : α) => coe a
#align with_bot.rec_bot_coe WithBot.recBotCoe

def unbot' (d : α) (x : WithBot α) : α :=
  recBotCoe d id x
#align with_bot.unbot' WithBot.unbot'

def map (f : α → β) : WithBot α → WithBot β :=
  Option.map f
#align with_bot.map WithBot.map

def map₂ : (α → β → γ) → WithBot α → WithBot β → WithBot γ := Option.map₂

lemma map₂_coe_coe (f : α → β → γ) (a : α) (b : β) : map₂ f a b = f a b := rfl
@[simp] lemma map₂_bot_left (f : α → β → γ) (b) : map₂ f ⊥ b = ⊥ := rfl
@[simp] lemma map₂_bot_right (f : α → β → γ) (a) : map₂ f a ⊥ = ⊥ := by cases a <;> rfl
@[simp] lemma map₂_coe_left (f : α → β → γ) (a : α) (b) : map₂ f a b = b.map fun b ↦ f a b := rfl
@[simp] lemma map₂_coe_right (f : α → β → γ) (a) (b : β) : map₂ f a b = a.map (f · b) := by
  cases a <;> rfl

@[simp] lemma map₂_eq_bot_iff {f : α → β → γ} {a : WithBot α} {b : WithBot β} :
    map₂ f a b = ⊥ ↔ a = ⊥ ∨ b = ⊥ := Option.map₂_eq_none_iff

theorem ne_bot_iff_exists {x : WithBot α} : x ≠ ⊥ ↔ ∃ a : α, ↑a = x :=
  Option.ne_none_iff_exists
#align with_bot.ne_bot_iff_exists WithBot.ne_bot_iff_exists

def unbot : ∀ x : WithBot α, x ≠ ⊥ → α | (x : α), _ => x
#align with_bot.unbot WithBot.unbot

def WithTop (α : Type*) :=
  Option α
#align with_top WithTop

def some : α → WithTop α :=
  Option.some

instance coeTC : CoeTC α (WithTop α) :=
  ⟨some⟩

instance top : Top (WithTop α) :=
  ⟨none⟩

instance inhabited : Inhabited (WithTop α) :=
  ⟨⊤⟩

instance nontrivial [Nonempty α] : Nontrivial (WithTop α) :=
  Option.nontrivial

open Function

theorem coe_injective : Injective ((↑) : α → WithTop α) :=
  Option.some_injective _

@[norm_cast]
theorem coe_inj : (a : WithTop α) = b ↔ a = b :=
  Option.some_inj

protected theorem «forall» {p : WithTop α → Prop} : (∀ x, p x) ↔ p ⊤ ∧ ∀ x : α, p x :=
  Option.forall
#align with_top.forall WithTop.forall

def recTopCoe {C : WithTop α → Sort*} (top : C ⊤) (coe : ∀ a : α, C a) : ∀ n : WithTop α, C n
  | none => top
  | Option.some a => coe a
#align with_top.rec_top_coe WithTop.recTopCoe

def toDual : WithTop α ≃ WithBot αᵒᵈ :=
  Equiv.refl _
#align with_top.to_dual WithTop.toDual

def ofDual : WithTop αᵒᵈ ≃ WithBot α :=
  Equiv.refl _
#align with_top.of_dual WithTop.ofDual

def _root_.WithBot.toDual : WithBot α ≃ WithTop αᵒᵈ :=
  Equiv.refl _
#align with_bot.to_dual WithBot.toDual

def _root_.WithBot.ofDual : WithBot αᵒᵈ ≃ WithTop α :=
  Equiv.refl _
#align with_bot.of_dual WithBot.ofDual

def untop' (d : α) (x : WithTop α) : α :=
  recTopCoe d id x
#align with_top.untop' WithTop.untop'

def map (f : α → β) : WithTop α → WithTop β :=
  Option.map f
#align with_top.map WithTop.map

def map₂ : (α → β → γ) → WithTop α → WithTop β → WithTop γ := Option.map₂

lemma map₂_coe_coe (f : α → β → γ) (a : α) (b : β) : map₂ f a b = f a b := rfl
@[simp] lemma map₂_top_left (f : α → β → γ) (b) : map₂ f ⊤ b = ⊤ := rfl
@[simp] lemma map₂_top_right (f : α → β → γ) (a) : map₂ f a ⊤ = ⊤ := by cases a <;> rfl
@[simp] lemma map₂_coe_left (f : α → β → γ) (a : α) (b) : map₂ f a b = b.map fun b ↦ f a b := rfl
@[simp] lemma map₂_coe_right (f : α → β → γ) (a) (b : β) : map₂ f a b = a.map (f · b) := by
  cases a <;> rfl

@[simp] lemma map₂_eq_top_iff {f : α → β → γ} {a : WithTop α} {b : WithTop β} :
    map₂ f a b = ⊤ ↔ a = ⊤ ∨ b = ⊤ := Option.map₂_eq_none_iff

theorem map_toDual (f : αᵒᵈ → βᵒᵈ) (a : WithBot α) :
    map f (WithBot.toDual a) = a.map (toDual ∘ f) :=
  rfl
#align with_top.map_to_dual WithTop.map_toDual

def untop : ∀ x : WithTop α, x ≠ ⊤ → α | (x : α), _ => x
#align with_top.untop WithTop.untop