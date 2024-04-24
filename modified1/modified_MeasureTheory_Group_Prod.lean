def MeasurableEquiv.shearMulRight [MeasurableInv G] : G × G ≃ᵐ G × G :=
  { Equiv.prodShear (Equiv.refl _) Equiv.mulLeft with
    measurable_toFun := measurable_fst.prod_mk measurable_mul
    measurable_invFun := measurable_fst.prod_mk <| measurable_fst.inv.mul measurable_snd }
#align measurable_equiv.shear_mul_right MeasurableEquiv.shearMulRight

def MeasurableEquiv.shearDivRight [MeasurableInv G] : G × G ≃ᵐ G × G :=
  { Equiv.prodShear (Equiv.refl _) Equiv.divRight with
    measurable_toFun := measurable_fst.prod_mk <| measurable_snd.div measurable_fst
    measurable_invFun := measurable_fst.prod_mk <| measurable_snd.mul measurable_fst }
#align measurable_equiv.shear_div_right MeasurableEquiv.shearDivRight