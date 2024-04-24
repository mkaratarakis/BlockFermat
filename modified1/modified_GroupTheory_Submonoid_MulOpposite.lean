def op (x : Submonoid M) : Submonoid Mᵐᵒᵖ where
  carrier := MulOpposite.unop ⁻¹' x
  mul_mem' ha hb := x.mul_mem hb ha
  one_mem' := Submonoid.one_mem' _

@[to_additive (attr := simp)]
theorem mem_op {x : Mᵐᵒᵖ} {S : Submonoid M} : x ∈ S.op ↔ x.unop ∈ S := Iff.rfl

/-- Pull an opposite submonoid back to a submonoid along `MulOpposite.op`-/
@[to_additive (attr := simps) "Pull an opposite additive submonoid back to a submonoid along
`AddOpposite.op`"]
protected def unop (x : Submonoid Mᵐᵒᵖ) : Submonoid M where
  carrier := MulOpposite.op ⁻¹' x
  mul_mem' ha hb := x.mul_mem hb ha
  one_mem' := Submonoid.one_mem' _

@[to_additive (attr := simp)]
theorem mem_unop {x : M} {S : Submonoid Mᵐᵒᵖ} : x ∈ S.unop ↔ MulOpposite.op x ∈ S := Iff.rfl

@[to_additive (attr := simp)]
theorem unop_op (S : Submonoid M) : S.op.unop = S := rfl

@[to_additive (attr := simp)]
theorem op_unop (S : Submonoid Mᵐᵒᵖ) : S.unop.op = S := rfl

/-! ### Lattice results -/