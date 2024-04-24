def Separable (f : R[X]) : Prop :=
  IsCoprime f (derivative f)
#align polynomial.separable Polynomial.Separable

def (f : R[X]) : f.Separable ↔ IsCoprime f (derivative f) :=
  Iff.rfl
#align polynomial.separable_def Polynomial.separable_def