def mulLeft [Distrib R] (r : R) : AddHom R R where
  toFun := (r * ·)
  map_add' := mul_add r
#align add_hom.mul_left AddHom.mulLeft

def mulRight [Distrib R] (r : R) : AddHom R R where
  toFun a := a * r
  map_add' _ _ := add_mul _ _ r
#align add_hom.mul_right AddHom.mulRight

def mulLeft [NonUnitalNonAssocSemiring R] (r : R) : R →+ R where
  toFun := (r * ·)
  map_zero' := mul_zero r
  map_add' := mul_add r
#align add_monoid_hom.mul_left AddMonoidHom.mulLeft

def mulRight [NonUnitalNonAssocSemiring R] (r : R) : R →+ R where
  toFun a := a * r
  map_zero' := zero_mul r
  map_add' _ _ := add_mul _ _ r
#align add_monoid_hom.mul_right AddMonoidHom.mulRight