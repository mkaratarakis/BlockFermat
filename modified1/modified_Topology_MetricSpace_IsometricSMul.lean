def constSMul (c : G) : X ≃ᵢ X where
  toEquiv := MulAction.toPerm c
  isometry_toFun := isometry_smul X c
#align isometry_equiv.const_smul IsometryEquiv.constSMul

def mulLeft [IsometricSMul G G] (c : G) : G ≃ᵢ G where
  toEquiv := Equiv.mulLeft c
  isometry_toFun := edist_mul_left c
#align isometry_equiv.mul_left IsometryEquiv.mulLeft

def mulRight [IsometricSMul Gᵐᵒᵖ G] (c : G) : G ≃ᵢ G where
  toEquiv := Equiv.mulRight c
  isometry_toFun a b := edist_mul_right a b c
#align isometry_equiv.mul_right IsometryEquiv.mulRight

def divRight [IsometricSMul Gᵐᵒᵖ G] (c : G) : G ≃ᵢ G where
  toEquiv := Equiv.divRight c
  isometry_toFun a b := edist_div_right a b c
#align isometry_equiv.div_right IsometryEquiv.divRight

def divLeft (c : G) : G ≃ᵢ G where
  toEquiv := Equiv.divLeft c
  isometry_toFun := edist_div_left c
#align isometry_equiv.div_left IsometryEquiv.divLeft

def inv : G ≃ᵢ G where
  toEquiv := Equiv.inv G
  isometry_toFun := edist_inv_inv
#align isometry_equiv.inv IsometryEquiv.inv