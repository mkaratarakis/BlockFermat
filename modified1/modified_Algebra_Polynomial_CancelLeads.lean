def cancelLeads : R[X] :=
  C p.leadingCoeff * X ^ (p.natDegree - q.natDegree) * q -
    C q.leadingCoeff * X ^ (q.natDegree - p.natDegree) * p
#align polynomial.cancel_leads Polynomial.cancelLeads