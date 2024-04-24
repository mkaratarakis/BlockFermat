def expOrderIso : ℝ ≃o Ioi (0 : ℝ) :=
  StrictMono.orderIsoOfSurjective _ (exp_strictMono.codRestrict exp_pos) <|
    (continuous_exp.subtype_mk _).surjective
      (by simp only [tendsto_Ioi_atTop, Subtype.coe_mk, tendsto_exp_atTop])
      (by simp [tendsto_exp_atBot_nhdsWithin])
#align real.exp_order_iso Real.expOrderIso