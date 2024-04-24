def eraseLead (f : R[X]) : R[X] :=
  Polynomial.erase f.natDegree f
#align polynomial.erase_lead Polynomial.eraseLead