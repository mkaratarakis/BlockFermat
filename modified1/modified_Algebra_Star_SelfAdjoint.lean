def IsSelfAdjoint [Star R] (x : R) : Prop :=
  star x = x
#align is_self_adjoint IsSelfAdjoint

def selfAdjoint [AddGroup R] [StarAddMonoid R] : AddSubgroup R where
  carrier := { x | IsSelfAdjoint x }
  zero_mem' := star_zero R
  add_mem' hx := hx.add
  neg_mem' hx := hx.neg
#align self_adjoint selfAdjoint

def skewAdjoint [AddCommGroup R] [StarAddMonoid R] : AddSubgroup R where
  carrier := { x | star x = -x }
  zero_mem' := show star (0 : R) = -0 by simp only [star_zero, neg_zero]
  add_mem' := @fun x y (hx : star x = -x) (hy : star y = -y) =>
    show star (x + y) = -(x + y) by rw [star_add x y, hx, hy, neg_add]
  neg_mem' := @fun x (hx : star x = -x) => show star (-x) = - -x by simp only [hx, star_neg]
#align skew_adjoint skewAdjoint