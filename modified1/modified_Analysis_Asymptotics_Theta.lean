def IsTheta (l : Filter α) (f : α → E) (g : α → F) : Prop :=
  IsBigO l f g ∧ IsBigO l g f
#align asymptotics.is_Theta Asymptotics.IsTheta