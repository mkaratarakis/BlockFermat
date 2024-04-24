def hasDistribPointwiseNeg {A} [Ring A] [Algebra R A] : HasDistribNeg (Submodule R A) :=
  toAddSubmonoid_injective.hasDistribNeg _ neg_toAddSubmonoid mul_toAddSubmonoid
#align submodule.has_distrib_pointwise_neg Submodule.hasDistribPointwiseNeg

def mapHom {A'} [Semiring A'] [Algebra R A'] (f : A →ₐ[R] A') : Submodule R A →*₀ Submodule R A'
    where
  toFun := map f.toLinearMap
  map_zero' := Submodule.map_bot _
  map_one' := Submodule.map_one _
  map_mul' _ _ := Submodule.map_mul _ _ _
#align submodule.map_hom Submodule.mapHom

def equivOpposite : Submodule R Aᵐᵒᵖ ≃+* (Submodule R A)ᵐᵒᵖ where
  toFun p := op <| p.comap (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A →ₗ[R] Aᵐᵒᵖ)
  invFun p := p.unop.comap (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ).symm : Aᵐᵒᵖ →ₗ[R] A)
  left_inv p := SetLike.coe_injective <| rfl
  right_inv p := unop_injective <| SetLike.coe_injective rfl
  map_add' p q := by simp [comap_equiv_eq_map_symm, ← op_add]
  map_mul' p q := congr_arg op <| comap_op_mul _ _
#align submodule.equiv_opposite Submodule.equivOpposite

def span.ringHom : SetSemiring A →+* Submodule R A where
  -- Note: the hint `(α := A)` is new in #8386

def pointwiseMulSemiringAction : MulSemiringAction α (Submodule R A) :=
  {
    Submodule.pointwiseDistribMulAction with
    smul_mul := fun r x y => Submodule.map_mul x y <| MulSemiringAction.toAlgHom R A r
    smul_one := fun r => Submodule.map_one <| MulSemiringAction.toAlgHom R A r }
#align submodule.pointwise_mul_semiring_action Submodule.pointwiseMulSemiringAction

def (s : SetSemiring A) (P : Submodule R A) :
    s • P = span R (SetSemiring.down (α := A) s) * P :=
  rfl
#align submodule.smul_def Submodule.smul_def

structure
protected theorem one_mul : (1 : Submodule R A) * M = M := by
  conv_lhs => rw [one_eq_span, ← span_eq M]
  erw [span_mul_span, one_mul, span_eq]
#align submodule.one_mul Submodule.one_mul

structure
protected theorem mul_one : M * 1 = M := by
  conv_lhs => rw [one_eq_span, ← span_eq M]
  erw [span_mul_span, mul_one, span_eq]
#align submodule.mul_one Submodule.mul_one