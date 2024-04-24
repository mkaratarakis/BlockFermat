structure on the completion
-/


open Set Filter UniformSpace Metric

open Filter Topology Uniformity

noncomputable section

universe u v

variable {α : Type u} {β : Type v} [PseudoMetricSpace α]

namespace UniformSpace.Completion

/-- The distance on the completion is obtained by extending the distance on the original space,
by uniform continuity. -/
instance : Dist (Completion α) :=
  ⟨Completion.extension₂ dist⟩

/-- The new distance is uniformly continuous. -/
protected theorem uniformContinuous_dist :
    UniformContinuous fun p : Completion α × Completion α ↦ dist p.1 p.2 :=
  uniformContinuous_extension₂ dist
#align uniform_space.completion.uniform_continuous_dist UniformSpace.Completion.uniformContinuous_dist

structure on the completion of a pseudo_metric space. -/
instance instMetricSpace : MetricSpace (Completion α) :=
  @MetricSpace.ofT0PseudoMetricSpace _
    { dist_self := Completion.dist_self
      dist_comm := Completion.dist_comm
      dist_triangle := Completion.dist_triangle
      dist := dist
      toUniformSpace := inferInstance
      uniformity_dist := Completion.uniformity_dist
      edist_dist := fun x y ↦ rfl } _
#align uniform_space.completion.metric_space UniformSpace.Completion.instMetricSpace