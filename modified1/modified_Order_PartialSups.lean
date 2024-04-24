def partialSups (f : ℕ → α) : ℕ →o α :=
  ⟨@Nat.rec (fun _ => α) (f 0) fun (n : ℕ) (a : α) => a ⊔ f (n + 1),
    monotone_nat_of_le_succ fun _ => le_sup_left⟩
#align partial_sups partialSups

def partialSups.gi : GaloisInsertion (partialSups : (ℕ → α) → ℕ →o α) (↑) where
  choice f h :=
    ⟨f, by convert (partialSups f).monotone using 1; exact (le_partialSups f).antisymm h⟩
  gc f g := by
    refine' ⟨(le_partialSups f).trans, fun h => _⟩
    convert partialSups_mono h
    exact OrderHom.ext _ _ g.monotone.partialSups_eq.symm
  le_l_u f := le_partialSups f
  choice_eq f h := OrderHom.ext _ _ ((le_partialSups f).antisymm h)
#align partial_sups.gi partialSups.gi