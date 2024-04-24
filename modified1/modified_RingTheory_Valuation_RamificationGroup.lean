def decompositionSubgroup (A : ValuationSubring L) : Subgroup (L ≃ₐ[K] L) :=
  MulAction.stabilizer (L ≃ₐ[K] L) A
#align valuation_subring.decomposition_subgroup ValuationSubring.decompositionSubgroup

def subMulAction (A : ValuationSubring L) : SubMulAction (A.decompositionSubgroup K) L where
  carrier := A
  smul_mem' g _ h := Set.mem_of_mem_of_subset (Set.smul_mem_smul_set h) g.prop.le
#align valuation_subring.sub_mul_action ValuationSubring.subMulAction

def inertiaSubgroup (A : ValuationSubring L) : Subgroup (A.decompositionSubgroup K) :=
  MonoidHom.ker <|
    MulSemiringAction.toRingAut (A.decompositionSubgroup K) (LocalRing.ResidueField A)
#align valuation_subring.inertia_subgroup ValuationSubring.inertiaSubgroup