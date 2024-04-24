def Splits (f : K[X]) : Prop :=
  f.map i = 0 ∨ ∀ {g : L[X]}, Irreducible g → g ∣ f.map i → degree g = 1
#align polynomial.splits Polynomial.Splits

def rootOfSplits' {f : K[X]} (hf : f.Splits i) (hfd : (f.map i).degree ≠ 0) : L :=
  Classical.choose <| exists_root_of_splits' i hf hfd
#align polynomial.root_of_splits' Polynomial.rootOfSplits'

def {i : K →+* L} {f : K[X]} (h : Splits i f) :
    f = 0 ∨ ∀ {g : L[X]}, Irreducible g → g ∣ f.map i → degree g = 1 :=
  (splits_iff i f).mp h
#align polynomial.splits.def Polynomial.Splits.def

def rootOfSplits {f : K[X]} (hf : f.Splits i) (hfd : f.degree ≠ 0) : L :=
  rootOfSplits' i hf ((f.degree_map i).symm ▸ hfd)
#align polynomial.root_of_splits Polynomial.rootOfSplits