structure on the multiplicative/additive opposite
-/

variable {α : Type*}

namespace MulOpposite

@[to_additive] instance instRatCast [RatCast α] : RatCast αᵐᵒᵖ := ⟨fun q ↦ op q⟩

@[to_additive (attr := simp, norm_cast)]
theorem op_ratCast [RatCast α] (q : ℚ) : op (q : α) = q :=
  rfl
#align mul_opposite.op_rat_cast MulOpposite.op_ratCast