def algebraMapCLM : R →L[R] A :=
  { Algebra.linearMap R A with
    toFun := algebraMap R A
    cont := continuous_algebraMap R A }
#align algebra_map_clm algebraMapCLM

def Subalgebra.topologicalClosure (s : Subalgebra R A) : Subalgebra R A :=
  { s.toSubsemiring.topologicalClosure with
    carrier := closure (s : Set A)
    algebraMap_mem' := fun r => s.toSubsemiring.le_topologicalClosure (s.algebraMap_mem r) }
#align subalgebra.topological_closure Subalgebra.topologicalClosure

def Subalgebra.commSemiringTopologicalClosure [T2Space A] (s : Subalgebra R A)
    (hs : ∀ x y : s, x * y = y * x) : CommSemiring s.topologicalClosure :=
  { s.topologicalClosure.toSemiring, s.toSubmonoid.commMonoidTopologicalClosure hs with }
#align subalgebra.comm_semiring_topological_closure Subalgebra.commSemiringTopologicalClosure

def Subalgebra.commRingTopologicalClosure [T2Space A] (s : Subalgebra R A)
    (hs : ∀ x y : s, x * y = y * x) : CommRing s.topologicalClosure :=
  { s.topologicalClosure.toRing, s.toSubmonoid.commMonoidTopologicalClosure hs with }
#align subalgebra.comm_ring_topological_closure Subalgebra.commRingTopologicalClosure

def Algebra.elementalAlgebra (x : A) : Subalgebra R A :=
  (Algebra.adjoin R ({x} : Set A)).topologicalClosure
#align algebra.elemental_algebra Algebra.elementalAlgebra