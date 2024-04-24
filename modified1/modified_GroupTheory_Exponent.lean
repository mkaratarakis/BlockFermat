def ExponentExists :=
  ∃ n, 0 < n ∧ ∀ g : G, g ^ n = 1
#align monoid.exponent_exists Monoid.ExponentExists

def exponent :=
  if h : ExponentExists G then Nat.find h else 0
#align monoid.exponent Monoid.exponent