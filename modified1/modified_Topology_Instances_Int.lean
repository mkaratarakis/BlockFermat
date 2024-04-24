structure of a metric space on `ℤ` is introduced in this file, induced from `ℝ`.
-/


noncomputable section

open Metric Set Filter

namespace Int

instance : Dist ℤ :=
  ⟨fun x y => dist (x : ℝ) y⟩

theorem dist_eq (x y : ℤ) : dist x y = |(x : ℝ) - y| := rfl
#align int.dist_eq Int.dist_eq