def Directed (f : ι → α) :=
  ∀ x y, ∃ z, f x ≼ f z ∧ f y ≼ f z
#align directed Directed

def DirectedOn (s : Set α) :=
  ∀ x ∈ s, ∀ y ∈ s, ∃ z ∈ s, x ≼ z ∧ y ≼ z
#align directed_on DirectedOn