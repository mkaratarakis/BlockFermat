def opHomeomorph : M ≃ₜ Mᵐᵒᵖ where
  toEquiv := opEquiv
  continuous_toFun := continuous_op
  continuous_invFun := continuous_unop
#align mul_opposite.op_homeomorph MulOpposite.opHomeomorph

structure on the opposite monoid and on the units group

In this file we define `TopologicalSpace` structure on `Mᵐᵒᵖ`, `Mᵃᵒᵖ`, `Mˣ`, and `AddUnits M`.
This file does not import definitions of a topological monoid and/or a continuous multiplicative
action, so we postpone the proofs of `HasContinuousMul Mᵐᵒᵖ` etc till we have these definitions.

## Tags

structure on the opposite monoid as on the original space. -/
@[to_additive "Put the same topological space structure on the opposite monoid as on the original
space."]
instance instTopologicalSpaceMulOpposite [TopologicalSpace M] : TopologicalSpace Mᵐᵒᵖ :=
  TopologicalSpace.induced (unop : Mᵐᵒᵖ → M) ‹_›

variable [TopologicalSpace M]

@[to_additive (attr := continuity)]
theorem continuous_unop : Continuous (unop : Mᵐᵒᵖ → M) :=
  continuous_induced_dom
#align mul_opposite.continuous_unop MulOpposite.continuous_unop