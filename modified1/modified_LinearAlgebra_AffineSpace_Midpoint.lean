def midpoint (x y : P) : P :=
  lineMap x y (⅟ 2 : R)
#align midpoint midpoint

def ofMapMidpoint (f : E → F) (h0 : f 0 = 0)
    (hm : ∀ x y, f (midpoint R x y) = midpoint R' (f x) (f y)) : E →+ F
    where
  toFun := f
  map_zero' := h0
  map_add' x y :=
    calc
      f (x + y) = f 0 + f (x + y) := by rw [h0, zero_add]
      _ = midpoint R' (f 0) (f (x + y)) + midpoint R' (f 0) (f (x + y)) :=
        (midpoint_add_self _ _ _).symm
      _ = f (midpoint R x y) + f (midpoint R x y) := by rw [← hm, midpoint_zero_add]
      _ = f x + f y := by rw [hm, midpoint_add_self]
#align add_monoid_hom.of_map_midpoint AddMonoidHom.ofMapMidpoint