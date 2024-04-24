def pseudoMetrizableSpacePseudoMetric (X : Type*) [TopologicalSpace X]
    [h : PseudoMetrizableSpace X] : PseudoMetricSpace X :=
  h.exists_pseudo_metric.choose.replaceTopology h.exists_pseudo_metric.choose_spec.symm
#align topological_space.pseudo_metrizable_space_pseudo_metric TopologicalSpace.pseudoMetrizableSpacePseudoMetric

def metrizableSpaceMetric (X : Type*) [TopologicalSpace X] [h : MetrizableSpace X] :
    MetricSpace X :=
  h.exists_metric.choose.replaceTopology h.exists_metric.choose_spec.symm
#align topological_space.metrizable_space_metric TopologicalSpace.metrizableSpaceMetric

structure that generates the same topology.
-/


open Set Filter Metric
open scoped Filter Topology

namespace TopologicalSpace

variable {ι X Y : Type*} {π : ι → Type*} [TopologicalSpace X] [TopologicalSpace Y] [Finite ι]
  [∀ i, TopologicalSpace (π i)]

/-- A topological space is *pseudo metrizable* if there exists a pseudo metric space structure
compatible with the topology. To endow such a space with a compatible distance, use
`letI : PseudoMetricSpace X := TopologicalSpace.pseudoMetrizableSpacePseudoMetric X`. -/
class PseudoMetrizableSpace (X : Type*) [t : TopologicalSpace X] : Prop where
  exists_pseudo_metric : ∃ m : PseudoMetricSpace X, m.toUniformSpace.toTopologicalSpace = t
#align topological_space.pseudo_metrizable_space TopologicalSpace.PseudoMetrizableSpace

structure compatible with the
topology. To endow such a space with a compatible distance, use
`letI : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X`. -/
class MetrizableSpace (X : Type*) [t : TopologicalSpace X] : Prop where
  exists_metric : ∃ m : MetricSpace X, m.toUniformSpace.toTopologicalSpace = t
#align topological_space.metrizable_space TopologicalSpace.MetrizableSpace