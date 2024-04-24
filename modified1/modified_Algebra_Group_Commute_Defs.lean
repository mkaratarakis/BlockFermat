def Commute {S : Type*} [Mul S] (a b : S) : Prop :=
  SemiconjBy a b b
#align commute Commute