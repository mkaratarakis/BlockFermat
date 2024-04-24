def IsSquare (a : α) : Prop :=
  ∃ r, a = r * r
#align is_square IsSquare

def Odd (a : α) : Prop :=
  ∃ k, a = 2 * k + 1
#align odd Odd