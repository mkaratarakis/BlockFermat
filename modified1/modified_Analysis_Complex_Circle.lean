def circle : Submonoid ℂ :=
  Submonoid.unitSphere ℂ
#align circle circle

def : ↑circle = { z : ℂ | abs z = 1 } :=
  Set.ext fun _ => mem_circle_iff_abs
#align circle_def circle_def

def circle.toUnits : circle →* Units ℂ :=
  unitSphereToUnits ℂ
#align circle.to_units circle.toUnits

def circle.ofConjDivSelf (z : ℂ) (hz : z ≠ 0) : circle :=
  ⟨conj z / z,
    mem_circle_iff_abs.2 <| by rw [map_div₀, abs_conj, div_self]; exact Complex.abs.ne_zero hz⟩
#align circle.of_conj_div_self circle.ofConjDivSelf

def expMapCircle : C(ℝ, circle) where
  toFun t := ⟨exp (t * I), by simp [exp_mul_I, abs_cos_add_sin_mul_I]⟩
#align exp_map_circle expMapCircle

def expMapCircleHom : ℝ →+ Additive circle where
  toFun := Additive.ofMul ∘ expMapCircle
  map_zero' := expMapCircle_zero
  map_add' := expMapCircle_add
#align exp_map_circle_hom expMapCircleHom

structure borrowed from `Metric.sphere`, the underlying set is
`{z : ℂ | abs (z - 0) = 1}`.  This prevents certain algebraic facts from working definitionally --
for example, the circle is not defeq to `{z : ℂ | abs z = 1}`, which is the kernel of `Complex.abs`
considered as a homomorphism from `ℂ` to `ℝ`, nor is it defeq to `{z : ℂ | normSq z = 1}`, which
is the kernel of the homomorphism `Complex.normSq` from `ℂ` to `ℝ`.

-/


noncomputable section

open Complex Metric

open ComplexConjugate

/-- The unit circle in `ℂ`, here given the structure of a submonoid of `ℂ`. -/
def circle : Submonoid ℂ :=
  Submonoid.unitSphere ℂ
#align circle circle