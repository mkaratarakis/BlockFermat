structure of a metric space on `ℚ` is introduced in this file, induced from `ℝ`.
-/


open Metric Set Filter

namespace Rat

instance : MetricSpace ℚ :=
  MetricSpace.induced (↑) Rat.cast_injective Real.metricSpace

theorem dist_eq (x y : ℚ) : dist x y = |(x : ℝ) - y| := rfl
#align rat.dist_eq Rat.dist_eq