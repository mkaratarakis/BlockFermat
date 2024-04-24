structure on the upper half plane.

In this file we define the complex manifold structure on the upper half-plane.
-/


open scoped UpperHalfPlane Manifold

namespace UpperHalfPlane

noncomputable instance : ChartedSpace ℂ ℍ :=
  UpperHalfPlane.openEmbedding_coe.singletonChartedSpace

instance : SmoothManifoldWithCorners 𝓘(ℂ) ℍ :=
  UpperHalfPlane.openEmbedding_coe.singleton_smoothManifoldWithCorners 𝓘(ℂ)

/-- The inclusion map `ℍ → ℂ` is a smooth map of manifolds. -/
theorem smooth_coe : Smooth 𝓘(ℂ) 𝓘(ℂ) ((↑) : ℍ → ℂ) := fun _ => contMDiffAt_extChartAt
#align upper_half_plane.smooth_coe UpperHalfPlane.smooth_coe