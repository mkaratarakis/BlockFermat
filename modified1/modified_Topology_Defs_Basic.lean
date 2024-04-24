def IsOpen : Set X → Prop := TopologicalSpace.IsOpen
#align is_open IsOpen

def IsClopen (s : Set X) : Prop :=
  IsClosed s ∧ IsOpen s
#align is_clopen IsClopen

def interior (s : Set X) : Set X :=
  ⋃₀ { t | IsOpen t ∧ t ⊆ s }
#align interior interior

def closure (s : Set X) : Set X :=
  ⋂₀ { t | IsClosed t ∧ s ⊆ t }
#align closure closure

def frontier (s : Set X) : Set X :=
  closure s \ interior s
#align frontier frontier

def Dense (s : Set X) : Prop :=
  ∀ x, x ∈ closure s
#align dense Dense

def DenseRange {α : Type*} (f : α → X) := Dense (range f)
#align dense_range DenseRange

def IsOpenMap (f : X → Y) : Prop := ∀ U : Set X, IsOpen U → IsOpen (f '' U)
#align is_open_map IsOpenMap

def IsClosedMap (f : X → Y) : Prop := ∀ U : Set X, IsClosed U → IsClosed (f '' U)
#align is_closed_map IsClosedMap

structure to make sure it is not unfolded by Lean. -/
@[fun_prop]
structure Continuous (f : X → Y) : Prop where
  /-- The preimage of an open set under a continuous function is an open set. Use `IsOpen.preimage`
  instead. -/
  isOpen_preimage : ∀ s, IsOpen s → IsOpen (f ⁻¹' s)
#align continuous Continuous