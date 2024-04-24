def IsTotallyDisconnected (s : Set α) : Prop :=
  ∀ t, t ⊆ s → IsPreconnected t → t.Subsingleton
#align is_totally_disconnected IsTotallyDisconnected

def IsTotallySeparated (s : Set α) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, x ≠ y →
    ∃ u v : Set α, IsOpen u ∧ IsOpen v ∧ x ∈ u ∧ y ∈ v ∧ s ⊆ u ∪ v ∧ Disjoint u v
#align is_totally_separated IsTotallySeparated

def Continuous.connectedComponentsLift (h : Continuous f) : ConnectedComponents α → β := fun x =>
  Quotient.liftOn' x f h.image_eq_of_connectedComponent_eq
#align continuous.connected_components_lift Continuous.connectedComponentsLift

def Continuous.connectedComponentsMap {β : Type*} [TopologicalSpace β] {f : α → β}
    (h : Continuous f) : ConnectedComponents α → ConnectedComponents β :=
  Continuous.connectedComponentsLift (ConnectedComponents.continuous_coe.comp h)
#align continuous.connected_components_map Continuous.connectedComponentsMap