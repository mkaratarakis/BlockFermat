def Angle : Type :=
  AddCircle (2 * π)
#align real.angle Real.Angle

def coe (r : ℝ) : Angle := QuotientAddGroup.mk r

instance : Coe ℝ Angle := ⟨Angle.coe⟩

instance : CircularOrder Real.Angle :=
  QuotientAddGroup.circularOrder (hp' := ⟨by norm_num [pi_pos]⟩)


@[continuity]
theorem continuous_coe : Continuous ((↑) : ℝ → Angle) :=
  continuous_quotient_mk'
#align real.angle.continuous_coe Real.Angle.continuous_coe

def coeHom : ℝ →+ Angle :=
  QuotientAddGroup.mk' _
#align real.angle.coe_hom Real.Angle.coeHom

def sin (θ : Angle) : ℝ :=
  sin_periodic.lift θ
#align real.angle.sin Real.Angle.sin

def cos (θ : Angle) : ℝ :=
  cos_periodic.lift θ
#align real.angle.cos Real.Angle.cos

def toReal (θ : Angle) : ℝ :=
  (toIocMod_periodic two_pi_pos (-π)).lift θ
#align real.angle.to_real Real.Angle.toReal

def tan (θ : Angle) : ℝ :=
  sin θ / cos θ
#align real.angle.tan Real.Angle.tan

def sign (θ : Angle) : SignType :=
  SignType.sign (sin θ)
#align real.angle.sign Real.Angle.sign