def Filter.ofCountableInter (l : Set (Set α))
    (hl : ∀ S : Set (Set α), S.Countable → S ⊆ l → ⋂₀ S ∈ l)
    (h_mono : ∀ s t, s ∈ l → s ⊆ t → t ∈ l) : Filter α where
  sets := l
  univ_sets := @sInter_empty α ▸ hl _ countable_empty (empty_subset _)
  sets_of_superset := h_mono _ _
  inter_sets {s t} hs ht := sInter_pair s t ▸
    hl _ ((countable_singleton _).insert _) (insert_subset_iff.2 ⟨hs, singleton_subset_iff.2 ht⟩)
#align filter.of_countable_Inter Filter.ofCountableInter

def Filter.ofCountableUnion (l : Set (Set α))
    (hUnion : ∀ S : Set (Set α), S.Countable → (∀ s ∈ S, s ∈ l) → ⋃₀ S ∈ l)
    (hmono : ∀ t ∈ l, ∀ s ⊆ t, s ∈ l) : Filter α := by
  refine .ofCountableInter {s | sᶜ ∈ l} (fun S hSc hSp ↦ ?_) fun s t ht hsub ↦ ?_
  · rw [mem_setOf_eq, compl_sInter]
    apply hUnion (compl '' S) (hSc.image _)
    intro s hs
    rw [mem_image] at hs
    rcases hs with ⟨t, ht, rfl⟩
    apply hSp ht
  · rw [mem_setOf_eq]
    rw [← compl_subset_compl] at hsub
    exact hmono sᶜ ht tᶜ hsub

instance Filter.countableInter_ofCountableUnion (l : Set (Set α)) (h₁ h₂) :
    CountableInterFilter (Filter.ofCountableUnion l h₁ h₂) :=
  countableInter_ofCountableInter ..

@[simp]
theorem Filter.mem_ofCountableUnion {l : Set (Set α)} {hunion hmono s} :
    s ∈ ofCountableUnion l hunion hmono ↔ l sᶜ :=
  Iff.rfl

instance countableInterFilter_principal (s : Set α) : CountableInterFilter (𝓟 s) :=
  ⟨fun _ _ hS => subset_sInter hS⟩
#align countable_Inter_filter_principal countableInterFilter_principal

def countableGenerate : Filter α :=
  ofCountableInter (CountableGenerateSets g) (fun _ => CountableGenerateSets.sInter) fun _ _ =>
    CountableGenerateSets.superset
  --deriving CountableInterFilter
#align filter.countable_generate Filter.countableGenerate