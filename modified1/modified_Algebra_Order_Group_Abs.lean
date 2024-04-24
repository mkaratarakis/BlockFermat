def mabs (a : α) : α := a ⊔ a⁻¹
#align has_abs.abs abs

def mabs.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $a) =>
    match a with
    | `(|$_|ₘ) | `(-$_) => `(|($a)|ₘ)
    | _ => `(|$a|ₘ)
  | _ => throw ()

/-- Unexpander for the notation `|a|` for `abs a`.
Tries to add discretionary parentheses in unparseable cases. -/
@[app_unexpander abs]
def abs.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $a) =>
    match a with
    | `(|$_|) | `(-$_) => `(|($a)|)
    | _ => `(|$a|)
  | _ => throw ()

@[to_additive] lemma mabs_le' : |a|ₘ ≤ b ↔ a ≤ b ∧ a⁻¹ ≤ b := sup_le_iff
#align abs_le' abs_le'

def IsSolid (s : Set α) : Prop := ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, |y| ≤ |x| → y ∈ s
#align lattice_ordered_add_comm_group.is_solid LatticeOrderedAddCommGroup.IsSolid

def solidClosure (s : Set α) : Set α := {y | ∃ x ∈ s, |y| ≤ |x|}
#align lattice_ordered_add_comm_group.solid_closure LatticeOrderedAddCommGroup.solidClosure