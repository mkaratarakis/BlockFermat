def pi : ℝ :=
  2 * Classical.choose exists_cos_eq_zero
#align real.pi Real.pi

def evalRealPi : PositivityExt where eval {u α} _zα _pα e := do
  match u, α, e with
  | 0, ~q(ℝ), ~q(Real.pi) =>
    assertInstancesCommute
    pure (.positive q(Real.pi_pos))
  | _, _, _ => throwError "not Real.pi"

end Mathlib.Meta.Positivity

namespace NNReal

open Real

open Real NNReal

/-- `π` considered as a nonnegative real. -/
noncomputable def pi : ℝ≥0 :=
  ⟨π, Real.pi_pos.le⟩
#align nnreal.pi NNReal.pi

def sqrtTwoAddSeries (x : ℝ) : ℕ → ℝ
  | 0 => x
  | n + 1 => √(2 + sqrtTwoAddSeries x n)
#align real.sqrt_two_add_series Real.sqrtTwoAddSeries

def sinOrderIso : Icc (-(π / 2)) (π / 2) ≃o Icc (-1 : ℝ) 1 :=
  (strictMonoOn_sin.orderIso _ _).trans <| OrderIso.setCongr _ _ bijOn_sin.image_eq
#align real.sin_order_iso Real.sinOrderIso