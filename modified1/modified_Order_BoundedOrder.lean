def topOrderOrNoTopOrder (α : Type*) [LE α] : PSum (OrderTop α) (NoTopOrder α) := by
  by_cases H : ∀ a : α, ∃ b, ¬b ≤ a
  · exact PSum.inr ⟨H⟩
  · push_neg at H
    letI : Top α := ⟨Classical.choose H⟩
    exact PSum.inl ⟨Classical.choose_spec H⟩
#align top_order_or_no_top_order topOrderOrNoTopOrder

def botOrderOrNoBotOrder (α : Type*) [LE α] : PSum (OrderBot α) (NoBotOrder α) := by
  by_cases H : ∀ a : α, ∃ b, ¬a ≤ b
  · exact PSum.inr ⟨H⟩
  · push_neg at H
    letI : Bot α := ⟨Classical.choose H⟩
    exact PSum.inl ⟨Classical.choose_spec H⟩
#align bot_order_or_no_bot_order botOrderOrNoBotOrder

def [∀ i, Bot (α' i)] : (⊥ : ∀ i, α' i) = fun _ => ⊥ :=
  rfl
#align pi.bot_def Pi.bot_def

def [∀ i, Top (α' i)] : (⊤ : ∀ i, α' i) = fun _ => ⊤ :=
  rfl
#align pi.top_def Pi.top_def

def OrderTop.lift [LE α] [Top α] [LE β] [OrderTop β] (f : α → β)
    (map_le : ∀ a b, f a ≤ f b → a ≤ b) (map_top : f ⊤ = ⊤) : OrderTop α :=
  ⟨fun a =>
    map_le _ _ <| by
      rw [map_top]
      -- Porting note: lean3 didn't need the type annotation
      exact @le_top β _ _ _⟩
#align order_top.lift OrderTop.lift

def OrderBot.lift [LE α] [Bot α] [LE β] [OrderBot β] (f : α → β)
    (map_le : ∀ a b, f a ≤ f b → a ≤ b) (map_bot : f ⊥ = ⊥) : OrderBot α :=
  ⟨fun a =>
    map_le _ _ <| by
      rw [map_bot]
      -- Porting note: lean3 didn't need the type annotation
      exact @bot_le β _ _ _⟩
#align order_bot.lift OrderBot.lift

def BoundedOrder.lift [LE α] [Top α] [Bot α] [LE β] [BoundedOrder β] (f : α → β)
    (map_le : ∀ a b, f a ≤ f b → a ≤ b) (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) :
    BoundedOrder α where
  __ := OrderTop.lift f map_le map_top
  __ := OrderBot.lift f map_le map_bot
#align bounded_order.lift BoundedOrder.lift

def orderBot [LE α] [OrderBot α] (hbot : p ⊥) : OrderBot { x : α // p x } where
  bot := ⟨⊥, hbot⟩
  bot_le _ := bot_le
#align subtype.order_bot Subtype.orderBot

def orderTop [LE α] [OrderTop α] (htop : p ⊤) : OrderTop { x : α // p x } where
  top := ⟨⊤, htop⟩
  le_top _ := le_top
#align subtype.order_top Subtype.orderTop

def boundedOrder [LE α] [BoundedOrder α] (hbot : p ⊥) (htop : p ⊤) :
    BoundedOrder (Subtype p) where
  __ := Subtype.orderTop htop
  __ := Subtype.orderBot hbot
#align subtype.bounded_order Subtype.boundedOrder