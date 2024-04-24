def centralizer [Mul M] : Set M :=
  { c | ∀ m ∈ S, m * c = c * m }
#align set.centralizer Set.centralizer

def centralizer : Subsemigroup M where
  carrier := S.centralizer
  mul_mem' := Set.mul_mem_centralizer
#align subsemigroup.centralizer Subsemigroup.centralizer