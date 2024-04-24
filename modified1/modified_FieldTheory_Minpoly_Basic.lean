def minpoly (x : B) : A[X] :=
  if hx : IsIntegral A x then degree_lt_wf.min _ hx else 0
#align minpoly minpoly