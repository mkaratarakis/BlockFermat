def coeWithTop {α} : α ↪ WithTop α :=
  { Embedding.some with toFun := WithTop.some }
#align function.embedding.coe_with_top Function.Embedding.coeWithTop

def optionElim {α β} (f : α ↪ β) (x : β) (h : x ∉ Set.range f) : Option α ↪ β :=
  ⟨Option.elim' x f, Option.injective_iff.2 ⟨f.2, h⟩⟩
#align function.embedding.option_elim Function.Embedding.optionElim

def optionEmbeddingEquiv (α β) : (Option α ↪ β) ≃ Σ f : α ↪ β, ↥(Set.range f)ᶜ where
  toFun f := ⟨coeWithTop.trans f, f none, fun ⟨x, hx⟩ ↦ Option.some_ne_none x <| f.injective hx⟩
  invFun f := f.1.optionElim f.2 f.2.2
  left_inv f := ext <| by rintro (_ | _) <;> simp [Option.coe_def]; rfl
  right_inv := fun ⟨f, y, hy⟩ ↦ by ext <;> simp [Option.coe_def]; rfl
#align function.embedding.option_embedding_equiv Function.Embedding.optionEmbeddingEquiv

def codRestrict {α β} (p : Set β) (f : α ↪ β) (H : ∀ a, f a ∈ p) : α ↪ p :=
  ⟨fun a ↦ ⟨f a, H a⟩, fun _ _ h ↦ f.injective (congr_arg Subtype.val h)⟩
#align function.embedding.cod_restrict Function.Embedding.codRestrict

def image {α β} (f : α ↪ β) : Set α ↪ Set β :=
  ⟨image f, f.2.image_injective⟩
#align function.embedding.image Function.Embedding.image

def embeddingOfSubset {α} (s t : Set α) (h : s ⊆ t) : s ↪ t :=
  ⟨fun x ↦ ⟨x.1, h x.2⟩, fun ⟨x, hx⟩ ⟨y, hy⟩ h ↦ by
    congr
    injection h⟩
#align set.embedding_of_subset Set.embeddingOfSubset

def subtypeOrEquiv (p q : α → Prop) [DecidablePred p] (h : Disjoint p q) :
    { x // p x ∨ q x } ≃ { x // p x } ⊕ { x // q x } where
  toFun := subtypeOrLeftEmbedding p q
  invFun :=
    Sum.elim (Subtype.impEmbedding _ _ fun x hx ↦ (Or.inl hx : p x ∨ q x))
      (Subtype.impEmbedding _ _ fun x hx ↦ (Or.inr hx : p x ∨ q x))
  left_inv x := by
    by_cases hx : p x
    · rw [subtypeOrLeftEmbedding_apply_left _ hx]
      simp [Subtype.ext_iff]
    · rw [subtypeOrLeftEmbedding_apply_right _ hx]
      simp [Subtype.ext_iff]
  right_inv x := by
    cases x with
    | inl x =>
        simp only [Sum.elim_inl]
        rw [subtypeOrLeftEmbedding_apply_left]
        · simp
        · simpa using x.prop
    | inr x =>
        simp only [Sum.elim_inr]
        rw [subtypeOrLeftEmbedding_apply_right]
        · simp
        · suffices ¬p x by simpa
          intro hp
          simpa using h.le_bot x ⟨hp, x.prop⟩
#align subtype_or_equiv subtypeOrEquiv