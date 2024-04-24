def Squarefree [Monoid R] (r : R) : Prop :=
  ∀ x : R, x * x ∣ r → IsUnit x
#align squarefree Squarefree