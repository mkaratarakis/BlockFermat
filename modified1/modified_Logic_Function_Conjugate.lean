def Semiconj (f : α → β) (ga : α → α) (gb : β → β) : Prop :=
  ∀ x, f (ga x) = gb (f x)
#align function.semiconj Function.Semiconj

def Commute (f g : α → α) : Prop :=
  Semiconj f g g
#align function.commute Function.Commute

def Semiconj₂ (f : α → β) (ga : α → α → α) (gb : β → β → β) : Prop :=
  ∀ x y, f (ga x y) = gb (f x) (f y)
#align function.semiconj₂ Function.Semiconj₂