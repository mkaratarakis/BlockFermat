structure `LocallyConvexFilterBasis`, extending `ModuleFilterBasis`, for filter
  bases generating a locally convex topology

-/


open TopologicalSpace Filter Set

open Topology Pointwise

section Semimodule

/-- A `LocallyConvexSpace` is a topological semimodule over an ordered semiring in which convex
neighborhoods of a point form a neighborhood basis at that point. -/
class LocallyConvexSpace (𝕜 E : Type*) [OrderedSemiring 𝕜] [AddCommMonoid E] [Module 𝕜 E]
    [TopologicalSpace E] : Prop where
  convex_basis : ∀ x : E, (𝓝 x).HasBasis (fun s : Set E => s ∈ 𝓝 x ∧ Convex 𝕜 s) id
#align locally_convex_space LocallyConvexSpace