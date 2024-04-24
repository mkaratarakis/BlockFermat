def MulOpposite (α : Type*) : Type _ := PreOpposite α
#align mul_opposite MulOpposite

def op : α → αᵐᵒᵖ :=
  PreOpposite.op'
#align mul_opposite.op MulOpposite.op

def unop : αᵐᵒᵖ → α :=
  PreOpposite.unop'
#align mul_opposite.unop MulOpposite.unop

def rec' {F : αᵐᵒᵖ → Sort*} (h : ∀ X, F (op X)) : ∀ X, F X := fun X ↦ h (unop X)
#align mul_opposite.rec MulOpposite.rec'

def opEquiv : α ≃ αᵐᵒᵖ :=
  ⟨op, unop, unop_op, op_unop⟩
#align mul_opposite.op_equiv MulOpposite.opEquiv

structure with one field, because it is not possible
to change the reducibility of a declaration after its definition, and because Lean 4 has
definitional eta reduction for structures (Lean 3 does not).

## Tags

structure PreOpposite (α : Type*) : Type _ where
  /-- The element of `PreOpposite α` that represents `x : α`. -/ op' ::
  /-- The element of `α` represented by `x : PreOpposite α`. -/ unop' : α

/-- Multiplicative opposite of a type. This type inherits all additive structures on `α` and
reverses left and right in multiplication. -/
@[to_additive
      "Additive opposite of a type. This type inherits all multiplicative structures on `α` and
      reverses left and right in addition."]
def MulOpposite (α : Type*) : Type _ := PreOpposite α
#align mul_opposite MulOpposite