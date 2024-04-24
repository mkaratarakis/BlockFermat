def padicValNat (p : ℕ) (n : ℕ) : ℕ :=
  if h : p ≠ 1 ∧ 0 < n then (multiplicity p n).get (multiplicity.finite_nat_iff.2 h) else 0
#align padic_val_nat padicValNat

def padicValInt (p : ℕ) (z : ℤ) : ℕ :=
  padicValNat p z.natAbs
#align padic_val_int padicValInt

def padicValRat (p : ℕ) (q : ℚ) : ℤ :=
  padicValInt p q.num - padicValNat p q.den
#align padic_val_rat padicValRat

def (p : ℕ) (q : ℚ) :
    padicValRat p q = padicValInt p q.num - padicValNat p q.den :=
  rfl

namespace padicValRat

open multiplicity

variable {p : ℕ}

/-- `padicValRat p q` is symmetric in `q`. -/
@[simp]
protected theorem neg (q : ℚ) : padicValRat p (-q) = padicValRat p q := by
  simp [padicValRat, padicValInt]
#align padic_val_rat.neg padicValRat.neg

def [hp : Fact p.Prime] {n : ℕ} (hn : 0 < n) :
    padicValNat p n = (multiplicity p n).get (multiplicity.finite_nat_iff.2 ⟨hp.out.ne_one, hn⟩) :=
  dif_pos ⟨hp.out.ne_one, hn⟩
#align padic_val_nat_def padicValNat_def

def (@Fact.out p.Prime).pos]
  simp
#align padic_val_nat_self padicValNat_self