def Simps.apply (f : AbsoluteValue R S) : R → S :=
  f
#align absolute_value.simps.apply AbsoluteValue.Simps.apply

def toMonoidWithZeroHom : R →*₀ S :=
  abv
#align absolute_value.to_monoid_with_zero_hom AbsoluteValue.toMonoidWithZeroHom

def toMonoidHom : R →* S :=
  abv
#align absolute_value.to_monoid_hom AbsoluteValue.toMonoidHom

def abs : AbsoluteValue S S where
  toFun := abs
  nonneg' := abs_nonneg
  eq_zero' _ := abs_eq_zero
  add_le' := abs_add
  map_mul' := abs_mul
#align absolute_value.abs AbsoluteValue.abs

def Mathlib.Meta.Positivity.evalAbv : PositivityExt where eval {_ _α} _zα _pα e := do
  let (.app f a) ← whnfR e | throwError "not abv ·"
  let pa' ← mkAppM ``abv_nonneg #[f, a]

def toAbsoluteValue : AbsoluteValue R S where
  toFun := abv
  add_le' := abv_add'
  eq_zero' _ := abv_eq_zero'
  nonneg' := abv_nonneg'
  map_mul' := abv_mul'
#align is_absolute_value.to_absolute_value IsAbsoluteValue.toAbsoluteValue

def abvHom [Nontrivial R] : R →*₀ S :=
  (toAbsoluteValue abv).toMonoidWithZeroHom
#align is_absolute_value.abv_hom IsAbsoluteValue.abvHom

def abvHom' : R →*₀ S where
  toFun := abv; map_zero' := abv_zero abv; map_one' := abv_one' abv; map_mul' := abv_mul abv
#align is_absolute_value.abv_hom' IsAbsoluteValue.abvHom'

structure AbsoluteValue (R S : Type*) [Semiring R] [OrderedSemiring S] extends R →ₙ* S where
  /-- The absolute value is nonnegative -/
  nonneg' : ∀ x, 0 ≤ toFun x
  /-- The absolute value is positive definitive -/
  eq_zero' : ∀ x, toFun x = 0 ↔ x = 0
  /-- The absolute value satisfies the triangle inequality -/
  add_le' : ∀ x y, toFun (x + y) ≤ toFun x + toFun y
#align absolute_value AbsoluteValue