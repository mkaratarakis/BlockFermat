def IsEquivalent (l : Filter α) (u v : α → β) :=
  (u - v) =o[l] v
#align asymptotics.is_equivalent Asymptotics.IsEquivalent