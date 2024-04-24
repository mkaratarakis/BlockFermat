def uniqueOfZeroEqOne (h : (0 : M₀) = 1) : Unique M₀ where
  default := 0
  uniq := eq_zero_of_zero_eq_one h
#align unique_of_zero_eq_one uniqueOfZeroEqOne