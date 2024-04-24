def extend (hs : LinearIndependent K ((↑) : s → V)) :
    Basis (hs.extend (subset_univ s)) K V :=
  Basis.mk
    (@LinearIndependent.restrict_of_comp_subtype _ _ _ id _ _ _ _ (hs.linearIndependent_extend _))
    (SetLike.coe_subset_coe.mp <| by simpa using hs.subset_span_extend (subset_univ s))
#align basis.extend Basis.extend

def sumExtendIndex (hs : LinearIndependent K v) : Set V :=
  LinearIndependent.extend hs.to_subtype_range (subset_univ _) \ range v

/-- If `v` is a linear independent family of vectors, extend it to a basis indexed by a sum type. -/
noncomputable def sumExtend (hs : LinearIndependent K v) : Basis (ι ⊕ sumExtendIndex hs) K V :=
  let s := Set.range v
  let e : ι ≃ s := Equiv.ofInjective v hs.injective
  let b := hs.to_subtype_range.extend (subset_univ (Set.range v))
  (Basis.extend hs.to_subtype_range).reindex <|
    Equiv.symm <|
      calc
        Sum ι (b \ s : Set V) ≃ Sum s (b \ s : Set V) := Equiv.sumCongr e (Equiv.refl _)
        _ ≃ b :=
          haveI := Classical.decPred (· ∈ s)
          Equiv.Set.sumDiffSubset (hs.to_subtype_range.subset_extend _)
#align basis.sum_extend Basis.sumExtend

def ofVectorSpaceIndex : Set V :=
  (linearIndependent_empty K V).extend (subset_univ _)
#align basis.of_vector_space_index Basis.ofVectorSpaceIndex

def ofVectorSpace : Basis (ofVectorSpaceIndex K V) K V :=
  Basis.extend (linearIndependent_empty K V)
#align basis.of_vector_space Basis.ofVectorSpace