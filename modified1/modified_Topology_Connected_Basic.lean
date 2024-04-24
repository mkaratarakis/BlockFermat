def IsPreconnected (s : Set α) : Prop :=
  ∀ u v : Set α, IsOpen u → IsOpen v → s ⊆ u ∪ v → (s ∩ u).Nonempty → (s ∩ v).Nonempty →
    (s ∩ (u ∩ v)).Nonempty
#align is_preconnected IsPreconnected

def IsConnected (s : Set α) : Prop :=
  s.Nonempty ∧ IsPreconnected s
#align is_connected IsConnected

def connectedComponent (x : α) : Set α :=
  ⋃₀ { s : Set α | IsPreconnected s ∧ x ∈ s }
#align connected_component connectedComponent

def connectedComponentIn (F : Set α) (x : α) : Set α :=
  if h : x ∈ F then (↑) '' connectedComponent (⟨x, h⟩ : F) else ∅
#align connected_component_in connectedComponentIn

def connectedComponentSetoid (α : Type*) [TopologicalSpace α] : Setoid α :=
  ⟨fun x y => connectedComponent x = connectedComponent y,
    ⟨fun x => by trivial, fun h1 => h1.symm, fun h1 h2 => h1.trans h2⟩⟩
#align connected_component_setoid connectedComponentSetoid

def ConnectedComponents (α : Type u) [TopologicalSpace α] :=
  Quotient (connectedComponentSetoid α)
#align connected_components ConnectedComponents

def mk : α → ConnectedComponents α := Quotient.mk''

instance : CoeTC α (ConnectedComponents α) := ⟨mk⟩

@[simp]
theorem coe_eq_coe {x y : α} :
    (x : ConnectedComponents α) = y ↔ connectedComponent x = connectedComponent y :=
  Quotient.eq''
#align connected_components.coe_eq_coe ConnectedComponents.coe_eq_coe