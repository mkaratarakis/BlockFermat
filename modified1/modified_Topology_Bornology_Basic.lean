def Bornology.cobounded (α : Type*) [Bornology α] : Filter α := Bornology.cobounded'
#align bornology.cobounded Bornology.cobounded

def Bornology.ofBounded {α : Type*} (B : Set (Set α))
    (empty_mem : ∅ ∈ B)
    (subset_mem : ∀ s₁ ∈ B, ∀ s₂ ⊆ s₁, s₂ ∈ B)
    (union_mem : ∀ s₁ ∈ B, ∀ s₂ ∈ B, s₁ ∪ s₂ ∈ B)
    (singleton_mem : ∀ x, {x} ∈ B) : Bornology α where
  cobounded' := comk (· ∈ B) empty_mem subset_mem union_mem
  le_cofinite' := by simpa [le_cofinite_iff_compl_singleton_mem]
#align bornology.of_bounded Bornology.ofBounded

def Bornology.ofBounded' {α : Type*} (B : Set (Set α))
    (empty_mem : ∅ ∈ B)
    (subset_mem : ∀ s₁ ∈ B, ∀ s₂ ⊆ s₁, s₂ ∈ B)
    (union_mem : ∀ s₁ ∈ B, ∀ s₂ ∈ B, s₁ ∪ s₂ ∈ B)
    (sUnion_univ : ⋃₀ B = univ) :
    Bornology α :=
  Bornology.ofBounded B empty_mem subset_mem union_mem fun x => by
    rw [sUnion_eq_univ_iff] at sUnion_univ
    rcases sUnion_univ x with ⟨s, hs, hxs⟩
    exact subset_mem s hs {x} (singleton_subset_iff.mpr hxs)
#align bornology.of_bounded' Bornology.ofBounded'

def IsCobounded [Bornology α] (s : Set α) : Prop :=
  s ∈ cobounded α
#align bornology.is_cobounded Bornology.IsCobounded

def IsBounded [Bornology α] (s : Set α) : Prop :=
  IsCobounded sᶜ
#align bornology.is_bounded Bornology.IsBounded

def {s : Set α} : IsCobounded s ↔ s ∈ cobounded α :=
  Iff.rfl
#align bornology.is_cobounded_def Bornology.isCobounded_def

def {s : Set α} : IsBounded s ↔ sᶜ ∈ cobounded α :=
  Iff.rfl
#align bornology.is_bounded_def Bornology.isBounded_def

def Bornology.cofinite : Bornology α where
  cobounded' := Filter.cofinite
  le_cofinite' := le_rfl
#align bornology.cofinite Bornology.cofinite

structure
fields explicit, we have to define these separately, prove the `ext` lemmas manually, and
initialize new `simps` projections. -/

/-- The filter of cobounded sets in a bornology. -/
def Bornology.cobounded (α : Type*) [Bornology α] : Filter α := Bornology.cobounded'
#align bornology.cobounded Bornology.cobounded