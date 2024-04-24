def UpperHalfPlane :=
  { point : ℂ // 0 < point.im }
#align upper_half_plane UpperHalfPlane

def coe (z : ℍ) : ℂ := z.1

-- Porting note: added to replace `deriving`
instance : CoeOut ℍ ℂ := ⟨UpperHalfPlane.coe⟩

instance : Inhabited ℍ :=
  ⟨⟨Complex.I, by simp⟩⟩

@[ext] theorem ext {a b : ℍ} (h : (a : ℂ) = b) : a = b := Subtype.eq h

@[simp, norm_cast] theorem ext_iff {a b : ℍ} : (a : ℂ) = b ↔ a = b := Subtype.coe_inj

instance canLift : CanLift ℂ ℍ ((↑) : ℍ → ℂ) fun z => 0 < z.im :=
  Subtype.canLift fun (z : ℂ) => 0 < z.im
#align upper_half_plane.can_lift UpperHalfPlane.canLift

def im (z : ℍ) :=
  (z : ℂ).im
#align upper_half_plane.im UpperHalfPlane.im

def re (z : ℍ) :=
  (z : ℂ).re
#align upper_half_plane.re UpperHalfPlane.re

def mk (z : ℂ) (h : 0 < z.im) : ℍ :=
  ⟨z, h⟩
#align upper_half_plane.mk UpperHalfPlane.mk

def evalUpperHalfPlaneIm : PositivityExt where eval {u α} _zα _pα e := do
  match u, α, e with
  | 0, ~q(ℝ), ~q(UpperHalfPlane.im $a) =>
    assertInstancesCommute
    pure (.positive q(@UpperHalfPlane.im_pos $a))
  | _, _, _ => throwError "not UpperHalfPlane.im"

/-- Extension for the `positivity` tactic: `UpperHalfPlane.coe`. -/
@[positivity UpperHalfPlane.coe _]
def evalUpperHalfPlaneCoe : PositivityExt where eval {u α} _zα _pα e := do
  match u, α, e with
  | 0, ~q(ℂ), ~q(UpperHalfPlane.coe $a) =>
    assertInstancesCommute
    pure (.nonzero q(@UpperHalfPlane.ne_zero $a))
  | _, _, _ => throwError "not UpperHalfPlane.coe"

end Mathlib.Meta.Positivity

namespace UpperHalfPlane

theorem normSq_pos (z : ℍ) : 0 < Complex.normSq (z : ℂ) := by
  rw [Complex.normSq_pos]; exact z.ne_zero
#align upper_half_plane.norm_sq_pos UpperHalfPlane.normSq_pos

def num (g : GL(2, ℝ)⁺) (z : ℍ) : ℂ :=
  (↑ₘg 0 0 : ℝ) * z + (↑ₘg 0 1 : ℝ)
#align upper_half_plane.num UpperHalfPlane.num

def denom (g : GL(2, ℝ)⁺) (z : ℍ) : ℂ :=
  (↑ₘg 1 0 : ℝ) * z + (↑ₘg 1 1 : ℝ)
#align upper_half_plane.denom UpperHalfPlane.denom

def smulAux' (g : GL(2, ℝ)⁺) (z : ℍ) : ℂ :=
  num g z / denom g z
#align upper_half_plane.smul_aux' UpperHalfPlane.smulAux'

def smulAux (g : GL(2, ℝ)⁺) (z : ℍ) : ℍ :=
  mk (smulAux' g z) <| by
    rw [smulAux'_im]
    convert mul_pos ((mem_glpos _).1 g.prop)
        (div_pos z.im_pos (Complex.normSq_pos.mpr (denom_ne_zero g z))) using 1
    simp only [GeneralLinearGroup.val_det_apply]
    ring
#align upper_half_plane.smul_aux UpperHalfPlane.smulAux

def coe' : SL(2, ℤ) → GL(2, ℝ)⁺ := fun g => ((g : SL(2, ℝ)) : GL(2, ℝ)⁺)

instance : Coe SL(2, ℤ) GL(2, ℝ)⁺ :=
  ⟨coe'⟩

@[simp]
theorem coe'_apply_complex {g : SL(2, ℤ)} {i j : Fin 2} :
    (Units.val <| Subtype.val <| coe' g) i j = (Subtype.val g i j : ℂ) :=
  rfl

@[simp]
theorem det_coe' {g : SL(2, ℤ)} : det (Units.val <| Subtype.val <| coe' g) = 1 := by
  simp only [SpecialLinearGroup.coe_GLPos_coe_GL_coe_matrix, SpecialLinearGroup.det_coe, coe']

instance SLOnGLPos : SMul SL(2, ℤ) GL(2, ℝ)⁺ :=
  ⟨fun s g => s * g⟩
#align upper_half_plane.SL_on_GL_pos UpperHalfPlane.ModularGroup.SLOnGLPos

structure of a `GLPos 2 ℝ` action by
fractional linear transformations.

We define the notation `ℍ` for the upper half plane available in the locale
`UpperHalfPlane` so as not to conflict with the quaternions.
-/

set_option linter.uppercaseLean3 false

noncomputable section

open Matrix Matrix.SpecialLinearGroup

open scoped Classical BigOperators MatrixGroups

/- Disable these instances as they are not the simp-normal form, and having them disabled ensures
we state lemmas in this file without spurious `coe_fn` terms. -/
attribute [-instance] Matrix.SpecialLinearGroup.instCoeFun
attribute [-instance] Matrix.GeneralLinearGroup.instCoeFun

local notation "GL(" n ", " R ")" "⁺" => Matrix.GLPos (Fin n) R
local notation:1024 "↑ₘ" A:1024 =>
  (((A : GL(2, ℝ)⁺) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) _)
local notation:1024 "↑ₘ[" R "]" A:1024 =>
  ((A : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R)

/-- The open upper half plane -/
def UpperHalfPlane :=
  { point : ℂ // 0 < point.im }
#align upper_half_plane UpperHalfPlane