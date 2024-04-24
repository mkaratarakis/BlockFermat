def : a ∣ b ↔ ∃ c, b = a * c :=
  Iff.rfl

alias dvd_iff_exists_eq_mul_right := dvd_def

theorem Dvd.elim {P : Prop} {a b : α} (H₁ : a ∣ b) (H₂ : ∀ c, b = a * c → P) : P :=
  Exists.elim H₁ H₂
#align dvd.elim Dvd.elim

def IsPrimal (a : α) : Prop := ∀ ⦃b c⦄, a ∣ b * c → ∃ a₁ a₂, a₁ ∣ b ∧ a₂ ∣ c ∧ a = a₁ * a₂

variable (α) in
/-- A monoid is a decomposition monoid if every element is primal. An integral domain whose
multiplicative monoid is a decomposition monoid, is called a pre-Schreier domain; it is a
Schreier domain if it is moreover integrally closed. -/
@[mk_iff] class DecompositionMonoid : Prop where
  primal (a : α) : IsPrimal a

theorem exists_dvd_and_dvd_of_dvd_mul [DecompositionMonoid α] {b c a : α} (H : a ∣ b * c) :
    ∃ a₁ a₂, a₁ ∣ b ∧ a₂ ∣ c ∧ a = a₁ * a₂ := DecompositionMonoid.primal a H
#align exists_dvd_and_dvd_of_dvd_mul exists_dvd_and_dvd_of_dvd_mul