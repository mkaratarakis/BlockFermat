def divisors : Finset ℕ :=
  Finset.filter (fun x : ℕ => x ∣ n) (Finset.Ico 1 (n + 1))
#align nat.divisors Nat.divisors

def properDivisors : Finset ℕ :=
  Finset.filter (fun x : ℕ => x ∣ n) (Finset.Ico 1 n)
#align nat.proper_divisors Nat.properDivisors

def divisorsAntidiagonal : Finset (ℕ × ℕ) :=
  Finset.filter (fun x => x.fst * x.snd = n) (Ico 1 (n + 1) ×ˢ Ico 1 (n + 1))
#align nat.divisors_antidiagonal Nat.divisorsAntidiagonal

def Perfect (n : ℕ) : Prop :=
  ∑ i in properDivisors n, i = n ∧ 0 < n
#align nat.perfect Nat.Perfect