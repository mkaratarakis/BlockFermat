def op (H : Subgroup G) : Subgroup Gᵐᵒᵖ where
  carrier := MulOpposite.unop ⁻¹' (H : Set G)
  one_mem' := H.one_mem
  mul_mem' ha hb := H.mul_mem hb ha
  inv_mem' := H.inv_mem

@[to_additive (attr := simp)]
theorem mem_op {x : Gᵐᵒᵖ} {S : Subgroup G} : x ∈ S.op ↔ x.unop ∈ S := Iff.rfl

@[to_additive (attr := simp)] lemma op_toSubmonoid (H : Subgroup G) :
    H.op.toSubmonoid = H.toSubmonoid.op :=
  rfl

/-- Pull an opposite subgroup back to a subgroup along `MulOpposite.op`-/
@[to_additive (attr := simps)
"Pull an opposite additive subgroup back to an additive subgroup along `AddOpposite.op`"]
protected def unop (H : Subgroup Gᵐᵒᵖ) : Subgroup G where
  carrier := MulOpposite.op ⁻¹' (H : Set Gᵐᵒᵖ)
  one_mem' := H.one_mem
  mul_mem' := fun ha hb => H.mul_mem hb ha
  inv_mem' := H.inv_mem

@[to_additive (attr := simp)]
theorem mem_unop {x : G} {S : Subgroup Gᵐᵒᵖ} : x ∈ S.unop ↔ MulOpposite.op x ∈ S := Iff.rfl

@[to_additive (attr := simp)] lemma unop_toSubmonoid (H : Subgroup Gᵐᵒᵖ) :
    H.unop.toSubmonoid = H.toSubmonoid.unop :=
  rfl

@[to_additive (attr := simp)]
theorem unop_op (S : Subgroup G) : S.op.unop = S := rfl

@[to_additive (attr := simp)]
theorem op_unop (S : Subgroup Gᵐᵒᵖ) : S.unop.op = S := rfl

/-! ### Lattice results -/

def opEquiv : Subgroup G ≃o Subgroup Gᵐᵒᵖ where
  toFun := Subgroup.op
  invFun := Subgroup.unop
  left_inv := unop_op
  right_inv := op_unop
  map_rel_iff' := op_le_op_iff
#align subgroup.opposite Subgroup.opEquiv

def equivOp (H : Subgroup G) : H ≃ H.op :=
  MulOpposite.opEquiv.subtypeEquiv fun _ => Iff.rfl
#align subgroup.opposite_equiv Subgroup.equivOp