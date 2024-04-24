def from "leanprover-community/mathlib"@"3a69562db5a458db8322b190ec8d9a8bbd8a5b14"

/-!
# Higher differentiability

def ContDiffWithinAt (n : ℕ∞) (f : E → F) (s : Set E) (x : E) : Prop :=
  ∀ m : ℕ, (m : ℕ∞) ≤ n → ∃ u ∈ 𝓝[insert x s] x,
    ∃ p : E → FormalMultilinearSeries 𝕜 E F, HasFTaylorSeriesUpToOn m f p u
#align cont_diff_within_at ContDiffWithinAt

def ContDiffOn (n : ℕ∞) (f : E → F) (s : Set E) : Prop :=
  ∀ x ∈ s, ContDiffWithinAt 𝕜 n f s x
#align cont_diff_on ContDiffOn

def iteratedFDerivWithin (n : ℕ) (f : E → F) (s : Set E) : E → E[×n]→L[𝕜] F :=
  Nat.recOn n (fun x => ContinuousMultilinearMap.curry0 𝕜 E (f x)) fun _ rec x =>
    ContinuousLinearMap.uncurryLeft (fderivWithin 𝕜 rec s x)
#align iterated_fderiv_within iteratedFDerivWithin

def ftaylorSeriesWithin (f : E → F) (s : Set E) (x : E) : FormalMultilinearSeries 𝕜 E F := fun n =>
  iteratedFDerivWithin 𝕜 n f s x
#align ftaylor_series_within ftaylorSeriesWithin

def ContDiffAt (n : ℕ∞) (f : E → F) (x : E) : Prop :=
  ContDiffWithinAt 𝕜 n f univ x
#align cont_diff_at ContDiffAt

def ContDiff (n : ℕ∞) (f : E → F) : Prop :=
  ∃ p : E → FormalMultilinearSeries 𝕜 E F, HasFTaylorSeriesUpTo n f p
#align cont_diff ContDiff

def iteratedFDeriv (n : ℕ) (f : E → F) : E → E[×n]→L[𝕜] F :=
  Nat.recOn n (fun x => ContinuousMultilinearMap.curry0 𝕜 E (f x)) fun _ rec x =>
    ContinuousLinearMap.uncurryLeft (fderiv 𝕜 rec x)
#align iterated_fderiv iteratedFDeriv

def ftaylorSeries (f : E → F) (x : E) : FormalMultilinearSeries 𝕜 E F := fun n =>
  iteratedFDeriv 𝕜 n f x
#align ftaylor_series ftaylorSeries

structure HasFTaylorSeriesUpToOn (n : ℕ∞) (f : E → F) (p : E → FormalMultilinearSeries 𝕜 E F)
  (s : Set E) : Prop where
  zero_eq : ∀ x ∈ s, (p x 0).uncurry0 = f x
  protected fderivWithin : ∀ m : ℕ, (m : ℕ∞) < n → ∀ x ∈ s,
    HasFDerivWithinAt (p · m) (p x m.succ).curryLeft s x
  cont : ∀ m : ℕ, (m : ℕ∞) ≤ n → ContinuousOn (p · m) s
#align has_ftaylor_series_up_to_on HasFTaylorSeriesUpToOn

structure HasFTaylorSeriesUpTo (n : ℕ∞) (f : E → F) (p : E → FormalMultilinearSeries 𝕜 E F) :
  Prop where
  zero_eq : ∀ x, (p x 0).uncurry0 = f x
  fderiv : ∀ m : ℕ, (m : ℕ∞) < n → ∀ x, HasFDerivAt (fun y => p y m) (p x m.succ).curryLeft x
  cont : ∀ m : ℕ, (m : ℕ∞) ≤ n → Continuous fun x => p x m
#align has_ftaylor_series_up_to HasFTaylorSeriesUpTo