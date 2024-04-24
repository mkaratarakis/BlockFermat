structure of a metric space on `ℕ` is introduced in this file, induced from `ℝ`.
-/

noncomputable section

open Metric Set Filter

namespace Nat

noncomputable instance : Dist ℕ :=
  ⟨fun x y => dist (x : ℝ) y⟩

theorem dist_eq (x y : ℕ) : dist x y = |(x : ℝ) - y| := rfl
#align nat.dist_eq Nat.dist_eq