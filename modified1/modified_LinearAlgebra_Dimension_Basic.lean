def Module.rank : Cardinal :=
  ⨆ ι : { s : Set M // LinearIndependent R ((↑) : s → M) }, (#ι.1)

def _ _).trans_le (ciSup_le' fun _ ↦ mk_set_le _)

lemma nonempty_linearIndependent_set : Nonempty {s : Set M // LinearIndependent R ((↑) : s → M)} :=
  ⟨⟨∅, linearIndependent_empty _ _⟩⟩

end

variable [Ring R] [Ring R'] [AddCommGroup M] [AddCommGroup M'] [AddCommGroup M₁]
variable [Module R M] [Module R M'] [Module R M₁] [Module R' M'] [Module R' M₁]

namespace LinearIndependent

variable [Nontrivial R]

theorem cardinal_lift_le_rank {ι : Type w} {v : ι → M}
    (hv : LinearIndependent R v) :
    Cardinal.lift.{v} #ι ≤ Cardinal.lift.{w} (Module.rank R M) := by