def IsPeriodicPt (f : α → α) (n : ℕ) (x : α) :=
  IsFixedPt f^[n] x
#align function.is_periodic_pt Function.IsPeriodicPt

def ptsOfPeriod (f : α → α) (n : ℕ) : Set α :=
  { x : α | IsPeriodicPt f n x }
#align function.pts_of_period Function.ptsOfPeriod

def periodicPts (f : α → α) : Set α :=
  { x : α | ∃ n > 0, IsPeriodicPt f n x }
#align function.periodic_pts Function.periodicPts

def minimalPeriod (f : α → α) (x : α) :=
  if h : x ∈ periodicPts f then Nat.find h else 0
#align function.minimal_period Function.minimalPeriod

def periodicOrbit (f : α → α) (x : α) : Cycle α :=
  (List.range (minimalPeriod f x)).map fun n => f^[n] x
#align function.periodic_orbit Function.periodicOrbit

def (f : α → α) (x : α) :
    periodicOrbit f x = (List.range (minimalPeriod f x)).map fun n => f^[n] x :=
  rfl
#align function.periodic_orbit_def Function.periodicOrbit_def

def period (m : M) (a : α) : ℕ := minimalPeriod (fun x => m • x) a

/-- `MulAction.period m a` is definitionally equal to `Function.minimalPeriod (m • ·) a`. -/
@[to_additive "`AddAction.period m a` is definitionally equal to
`Function.minimalPeriod (m +ᵥ ·) a`"]
theorem period_eq_minimalPeriod {m : M} {a : α} :
    MulAction.period m a = minimalPeriod (fun x => m • x) a := rfl

/-- `m ^ (period m a)` fixes `a`. -/
@[to_additive (attr := simp) "`(period m a) • m` fixes `a`."]
theorem pow_period_smul (m : M) (a : α) : m ^ (period m a) • a = a := by
  rw [period_eq_minimalPeriod, ← smul_iterate_apply, iterate_minimalPeriod]

@[to_additive]
lemma isPeriodicPt_smul_iff {m : M} {a : α} {n : ℕ} :
    IsPeriodicPt (m • ·) n a ↔ m ^ n • a = a := by
  rw [← smul_iterate_apply, IsPeriodicPt, IsFixedPt]

/-! ### Multiples of `MulAction.period`