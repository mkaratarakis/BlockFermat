def h, integral_undef H]

theorem integral_prod_mul {L : Type*} [RCLike L] (f : α → L) (g : β → L) :
    ∫ z, f z.1 * g z.2 ∂μ.prod ν = (∫ x, f x ∂μ) * ∫ y, g y ∂ν :=
  integral_prod_smul f g
#align measure_theory.integral_prod_mul MeasureTheory.integral_prod_mul