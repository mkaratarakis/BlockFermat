def IsLeftRegular (c : R) :=
  (c * ·).Injective
#align is_left_regular IsLeftRegular

def IsRightRegular (c : R) :=
  (· * c).Injective
#align is_right_regular IsRightRegular

structure IsAddRegular {R : Type*} [Add R] (c : R) : Prop where
  /-- An add-regular element `c` is left-regular -/
  left : IsAddLeftRegular c -- Porting note: It seems like to_additive is misbehaving
  /-- An add-regular element `c` is right-regular -/
  right : IsAddRightRegular c
#align is_add_regular IsAddRegular

structure IsRegular (c : R) : Prop where
  /-- A regular element `c` is left-regular -/
  left : IsLeftRegular c
  /-- A regular element `c` is right-regular -/
  right : IsRightRegular c
#align is_regular IsRegular