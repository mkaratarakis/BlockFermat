def toComplₗᵢ : E →ₗᵢ[𝕜] Completion E :=
  { toCompl with
    toFun := (↑)
    map_smul' := coe_smul
    norm_map' := norm_coe }
#align uniform_space.completion.to_complₗᵢ UniformSpace.Completion.toComplₗᵢ

def toComplL : E →L[𝕜] Completion E :=
  toComplₗᵢ.toContinuousLinearMap
set_option linter.uppercaseLean3 false in
#align uniform_space.completion.to_complL UniformSpace.Completion.toComplL

structure on the completion of a normed space

If `E` is a normed space over `𝕜`, then so is `UniformSpace.Completion E`. In this file we provide
necessary instances and define `UniformSpace.Completion.toComplₗᵢ` - coercion
`E → UniformSpace.Completion E` as a bundled linear isometry.

We also show that if `A` is a normed algebra over `𝕜`, then so is `UniformSpace.Completion A`.

TODO: Generalise the results here from the concrete `completion` to any `AbstractCompletion`.
-/


noncomputable section

namespace UniformSpace

namespace Completion

variable (𝕜 E : Type*) [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

instance (priority := 100) NormedSpace.to_uniformContinuousConstSMul :
    UniformContinuousConstSMul 𝕜 E :=
  ⟨fun c => (lipschitzWith_smul c).uniformContinuous⟩
#align uniform_space.completion.normed_space.to_has_uniform_continuous_const_smul UniformSpace.Completion.NormedSpace.to_uniformContinuousConstSMul