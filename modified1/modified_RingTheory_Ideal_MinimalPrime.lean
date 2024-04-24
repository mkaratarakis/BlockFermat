def Ideal.minimalPrimes : Set (Ideal R) :=
  minimals (· ≤ ·) { p | p.IsPrime ∧ I ≤ p }
#align ideal.minimal_primes Ideal.minimalPrimes

def minimalPrimes : Set (Ideal R) :=
  Ideal.minimalPrimes ⊥
#align minimal_primes minimalPrimes