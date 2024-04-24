def jacobson (I : Ideal R) : Ideal R :=
  sInf { J : Ideal R | I ≤ J ∧ IsMaximal J }
#align ideal.jacobson Ideal.jacobson