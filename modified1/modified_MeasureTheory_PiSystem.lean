def IsPiSystem {α} (C : Set (Set α)) : Prop :=
  ∀ᵉ (s ∈ C) (t ∈ C), (s ∩ t : Set α).Nonempty → s ∩ t ∈ C
#align is_pi_system IsPiSystem

def piiUnionInter (π : ι → Set (Set α)) (S : Set ι) : Set (Set α) :=
  { s : Set α |
    ∃ (t : Finset ι) (_ : ↑t ⊆ S) (f : ι → Set α) (_ : ∀ x, x ∈ t → f x ∈ π x), s = ⋂ x ∈ t, f x }
#align pi_Union_Inter piiUnionInter

def {α} {a b : DynkinSystem α} : a ≤ b ↔ a.Has ≤ b.Has :=
  Iff.rfl
#align measurable_space.dynkin_system.le_def MeasurableSpace.DynkinSystem.le_def

def ofMeasurableSpace (m : MeasurableSpace α) : DynkinSystem α
    where
  Has := m.MeasurableSet'
  has_empty := m.measurableSet_empty
  has_compl {a} := m.measurableSet_compl a
  has_iUnion_nat {f} _ hf := m.measurableSet_iUnion f hf
#align measurable_space.dynkin_system.of_measurable_space MeasurableSpace.DynkinSystem.ofMeasurableSpace

def generate (s : Set (Set α)) : DynkinSystem α
    where
  Has := GenerateHas s
  has_empty := GenerateHas.empty
  has_compl {_} := GenerateHas.compl
  has_iUnion_nat {_} := GenerateHas.iUnion
#align measurable_space.dynkin_system.generate MeasurableSpace.DynkinSystem.generate

def {C : Set (Set α)} : (generate C).Has = GenerateHas C :=
  rfl
#align measurable_space.dynkin_system.generate_has_def MeasurableSpace.DynkinSystem.generateHas_def

def toMeasurableSpace (h_inter : ∀ s₁ s₂, d.Has s₁ → d.Has s₂ → d.Has (s₁ ∩ s₂)) :
    MeasurableSpace α where
  MeasurableSet' := d.Has
  measurableSet_empty := d.has_empty
  measurableSet_compl s h := d.has_compl h
  measurableSet_iUnion f hf := by
    rw [← iUnion_disjointed]
    exact
      d.has_iUnion (disjoint_disjointed _) fun n =>
        disjointedRec (fun (t : Set α) i h => h_inter _ _ h <| d.has_compl <| hf i) (hf n)
#align measurable_space.dynkin_system.to_measurable_space MeasurableSpace.DynkinSystem.toMeasurableSpace

def restrictOn {s : Set α} (h : d.Has s) : DynkinSystem α where
  -- Porting note(#12129): additional beta reduction needed

structure DynkinSystem (α : Type*) where
  /-- Predicate saying that a given set is contained in the Dynkin system. -/
  Has : Set α → Prop
  /-- A Dynkin system contains the empty set. -/
  has_empty : Has ∅
  /-- A Dynkin system is closed under complementation. -/
  has_compl : ∀ {a}, Has a → Has aᶜ
  /-- A Dynkin system is closed under countable union of pairwise disjoint sets. Use a more general
  `MeasurableSpace.DynkinSystem.has_iUnion` instead. -/
  has_iUnion_nat : ∀ {f : ℕ → Set α}, Pairwise (Disjoint on f) → (∀ i, Has (f i)) → Has (⋃ i, f i)
#align measurable_space.dynkin_system MeasurableSpace.DynkinSystem