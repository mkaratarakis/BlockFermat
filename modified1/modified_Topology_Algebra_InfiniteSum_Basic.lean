structure on the target should go in `Group.lean`.

-/

noncomputable section

open Filter Finset Function

open scoped BigOperators Topology

variable {α β γ δ : Type*}

section HasProd

variable [CommMonoid α] [TopologicalSpace α]
variable {f g : β → α} {a b : α} {s : Finset β}

/-- Constant one function has product `1` -/
@[to_additive "Constant zero function has sum `0`"]
theorem hasProd_one : HasProd (fun _ ↦ 1 : β → α) 1 := by simp [HasProd, tendsto_const_nhds]
#align has_sum_zero hasSum_zero