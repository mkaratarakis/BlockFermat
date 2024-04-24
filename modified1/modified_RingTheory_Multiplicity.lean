def multiplicity [Monoid α] [DecidableRel ((· ∣ ·) : α → α → Prop)] (a b : α) : PartENat :=
  PartENat.find fun n => ¬a ^ (n + 1) ∣ b
#align multiplicity multiplicity

def Finite (a b : α) : Prop :=
  ∃ n : ℕ, ¬a ^ (n + 1) ∣ b
#align multiplicity.finite multiplicity.Finite

def {a b : α} : Finite a b ↔ ∃ n : ℕ, ¬a ^ (n + 1) ∣ b :=
  Iff.rfl
#align multiplicity.finite_def multiplicity.finite_def

def ℕ, ← @finite_iff_dom ℤ, @finite_def ℤ]
    norm_cast
  · intro h1 h2
    apply _root_.le_antisymm <;>
      · apply Nat.find_mono
        norm_cast
        simp
#align multiplicity.int.coe_nat_multiplicity multiplicity.Int.natCast_multiplicity