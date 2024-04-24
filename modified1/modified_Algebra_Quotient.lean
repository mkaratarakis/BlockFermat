def HasQuotient.Quotient (A : outParam <| Type u) {B : Type v}
    [HasQuotient A B] (b : B) : Type max u v :=
  HasQuotient.quotient' b
#align has_quotient.quotient HasQuotient.Quotient