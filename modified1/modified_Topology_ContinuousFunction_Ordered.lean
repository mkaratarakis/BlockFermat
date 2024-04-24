def [PartialOrder β] {f g : C(α, β)} : f ≤ g ↔ ∀ a, f a ≤ g a :=
  Pi.le_def
#align continuous_map.le_def ContinuousMap.le_def

def [PartialOrder β] {f g : C(α, β)} : f < g ↔ (∀ a, f a ≤ g a) ∧ ∃ a, f a < g a :=
  Pi.lt_def
#align continuous_map.lt_def ContinuousMap.lt_def

def IccExtend (f : C(Set.Icc a b, β)) : C(α, β) where
  toFun := Set.IccExtend h f
#align continuous_map.Icc_extend ContinuousMap.IccExtend

structure (given by pointwise min and max)
on continuous functions.
-/

instance partialOrder [PartialOrder β] : PartialOrder C(α, β) :=
  PartialOrder.lift (fun f => f.toFun) (fun f g _ => by cases f; cases g; congr)
  -- Porting note: was `by tidy`, and `by aesop` alone didn't work
#align continuous_map.partial_order ContinuousMap.partialOrder

structure to `BoundedContinuousFunction`

section Extend

variable [LinearOrder α] [OrderTopology α] {a b : α} (h : a ≤ b)

/-- Extend a continuous function `f : C(Set.Icc a b, β)` to a function `f : C(α, β)`.  -/
def IccExtend (f : C(Set.Icc a b, β)) : C(α, β) where
  toFun := Set.IccExtend h f
#align continuous_map.Icc_extend ContinuousMap.IccExtend