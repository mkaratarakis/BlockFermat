def IsGenericPoint (x : α) (S : Set α) : Prop :=
  closure ({x} : Set α) = S
#align is_generic_point IsGenericPoint

def {x : α} {S : Set α} : IsGenericPoint x S ↔ closure ({x} : Set α) = S :=
  Iff.rfl
#align is_generic_point_def isGenericPoint_def

def {x : α} {S : Set α} (h : IsGenericPoint x S) :
    closure ({x} : Set α) = S :=
  h
#align is_generic_point.def IsGenericPoint.def

def ▸ isClosed_closure
#align is_generic_point.is_closed IsGenericPoint.isClosed

def ▸ isIrreducible_singleton.closure
#align is_generic_point.is_irreducible IsGenericPoint.isIrreducible

def IsIrreducible.genericPoint [QuasiSober α] {S : Set α} (hS : IsIrreducible S) :
    α :=
  (QuasiSober.sober hS.closure isClosed_closure).choose
#align is_irreducible.generic_point IsIrreducible.genericPoint

def genericPoint [QuasiSober α] [IrreducibleSpace α] : α :=
  (IrreducibleSpace.isIrreducible_univ α).genericPoint
#align generic_point genericPoint

def irreducibleSetEquivPoints [QuasiSober α] [T0Space α] :
    { s : Set α | IsIrreducible s ∧ IsClosed s } ≃o α where
  toFun s := s.prop.1.genericPoint
  invFun x := ⟨closure ({x} : Set α), isIrreducible_singleton.closure, isClosed_closure⟩
  left_inv s := Subtype.eq <| Eq.trans s.prop.1.genericPoint_spec <|
    closure_eq_iff_isClosed.mpr s.2.2
  right_inv x := isIrreducible_singleton.closure.genericPoint_spec.eq
      (by rw [closure_closure]; exact isGenericPoint_closure)
  map_rel_iff' := by
    rintro ⟨s, hs⟩ ⟨t, ht⟩
    refine specializes_iff_closure_subset.trans ?_
    simp [hs.2.closure_eq, ht.2.closure_eq]
#align irreducible_set_equiv_points irreducibleSetEquivPoints