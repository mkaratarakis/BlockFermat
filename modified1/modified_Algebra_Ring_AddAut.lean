def mulLeft : Rˣ →* AddAut R :=
  DistribMulAction.toAddAut _ _
#align add_aut.mul_left AddAut.mulLeft

def mulRight (u : Rˣ) : AddAut R :=
  DistribMulAction.toAddAut Rᵐᵒᵖˣ R (Units.opEquiv.symm <| MulOpposite.op u)
#align add_aut.mul_right AddAut.mulRight