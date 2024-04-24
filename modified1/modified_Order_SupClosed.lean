def SupClosed (s : Set α) : Prop := ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → a ⊔ b ∈ s

@[simp] lemma supClosed_empty : SupClosed (∅ : Set α) := by simp [SupClosed]
@[simp] lemma supClosed_singleton : SupClosed ({a} : Set α) := by simp [SupClosed]

@[simp] lemma supClosed_univ : SupClosed (univ : Set α) := by simp [SupClosed]
lemma SupClosed.inter (hs : SupClosed s) (ht : SupClosed t) : SupClosed (s ∩ t) :=
  fun _a ha _b hb ↦ ⟨hs ha.1 hb.1, ht ha.2 hb.2⟩

lemma supClosed_sInter (hS : ∀ s ∈ S, SupClosed s) : SupClosed (⋂₀ S) :=
  fun _a ha _b hb _s hs ↦ hS _ hs (ha _ hs) (hb _ hs)

lemma supClosed_iInter (hf : ∀ i, SupClosed (f i)) : SupClosed (⋂ i, f i) :=
  supClosed_sInter <| forall_mem_range.2 hf

lemma SupClosed.directedOn (hs : SupClosed s) : DirectedOn (· ≤ ·) s :=
  fun _a ha _b hb ↦ ⟨_, hs ha hb, le_sup_left, le_sup_right⟩

lemma IsUpperSet.supClosed (hs : IsUpperSet s) : SupClosed s := fun _a _ _b ↦ hs le_sup_right

lemma SupClosed.preimage [FunLike F β α] [SupHomClass F β α] (hs : SupClosed s) (f : F) :
    SupClosed (f ⁻¹' s) :=
  fun a ha b hb ↦ by simpa [map_sup] using hs ha hb

lemma SupClosed.image [FunLike F α β] [SupHomClass F α β] (hs : SupClosed s) (f : F) :
    SupClosed (f '' s) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  rw [← map_sup]
  exact Set.mem_image_of_mem _ <| hs ha hb

lemma supClosed_range [FunLike F α β] [SupHomClass F α β] (f : F) : SupClosed (Set.range f) := by
  simpa using supClosed_univ.image f

lemma SupClosed.prod {t : Set β} (hs : SupClosed s) (ht : SupClosed t) : SupClosed (s ×ˢ t) :=
  fun _a ha _b hb ↦ ⟨hs ha.1 hb.1, ht ha.2 hb.2⟩

lemma supClosed_pi {ι : Type*} {α : ι → Type*} [∀ i, SemilatticeSup (α i)] {s : Set ι}
    {t : ∀ i, Set (α i)} (ht : ∀ i ∈ s, SupClosed (t i)) : SupClosed (s.pi t) :=
  fun _a ha _b hb _i hi ↦ ht _ hi (ha _ hi) (hb _ hi)

end Set

section Finset
variable {ι : Type*} {f : ι → α} {s : Set α} {t : Finset ι} {a : α}
open Finset

lemma SupClosed.finsetSup'_mem (hs : SupClosed s) (ht : t.Nonempty) :
    (∀ i ∈ t, f i ∈ s) → t.sup' ht f ∈ s :=
  sup'_induction _ _ hs

lemma SupClosed.finsetSup_mem [OrderBot α] (hs : SupClosed s) (ht : t.Nonempty) :
    (∀ i ∈ t, f i ∈ s) → t.sup f ∈ s :=
  sup'_eq_sup ht f ▸ hs.finsetSup'_mem ht
#align finset.sup_closed_of_sup_closed SupClosed.finsetSup_mem

def InfClosed (s : Set α) : Prop := ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → a ⊓ b ∈ s

@[simp] lemma infClosed_empty : InfClosed (∅ : Set α) := by simp [InfClosed]
@[simp] lemma infClosed_singleton : InfClosed ({a} : Set α) := by simp [InfClosed]

@[simp] lemma infClosed_univ : InfClosed (univ : Set α) := by simp [InfClosed]
lemma InfClosed.inter (hs : InfClosed s) (ht : InfClosed t) : InfClosed (s ∩ t) :=
  fun _a ha _b hb ↦ ⟨hs ha.1 hb.1, ht ha.2 hb.2⟩

lemma infClosed_sInter (hS : ∀ s ∈ S, InfClosed s) : InfClosed (⋂₀ S) :=
  fun _a ha _b hb _s hs ↦ hS _ hs (ha _ hs) (hb _ hs)

lemma infClosed_iInter (hf : ∀ i, InfClosed (f i)) : InfClosed (⋂ i, f i) :=
  infClosed_sInter <| forall_mem_range.2 hf

lemma InfClosed.codirectedOn (hs : InfClosed s) : DirectedOn (· ≥ ·) s :=
  fun _a ha _b hb ↦ ⟨_, hs ha hb, inf_le_left, inf_le_right⟩

lemma IsLowerSet.infClosed (hs : IsLowerSet s) : InfClosed s := fun _a _ _b ↦ hs inf_le_right

lemma InfClosed.preimage [FunLike F β α] [InfHomClass F β α] (hs : InfClosed s) (f : F) :
    InfClosed (f ⁻¹' s) :=
  fun a ha b hb ↦ by simpa [map_inf] using hs ha hb

lemma InfClosed.image [FunLike F α β] [InfHomClass F α β] (hs : InfClosed s) (f : F) :
    InfClosed (f '' s) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  rw [← map_inf]
  exact Set.mem_image_of_mem _ <| hs ha hb

lemma infClosed_range [FunLike F α β] [InfHomClass F α β] (f : F) : InfClosed (Set.range f) := by
  simpa using infClosed_univ.image f

lemma InfClosed.prod {t : Set β} (hs : InfClosed s) (ht : InfClosed t) : InfClosed (s ×ˢ t) :=
  fun _a ha _b hb ↦ ⟨hs ha.1 hb.1, ht ha.2 hb.2⟩

lemma infClosed_pi {ι : Type*} {α : ι → Type*} [∀ i, SemilatticeInf (α i)] {s : Set ι}
    {t : ∀ i, Set (α i)} (ht : ∀ i ∈ s, InfClosed (t i)) : InfClosed (s.pi t) :=
  fun _a ha _b hb _i hi ↦ ht _ hi (ha _ hi) (hb _ hi)

end Set

section Finset
variable {ι : Type*} {f : ι → α} {s : Set α} {t : Finset ι} {a : α}
open Finset

lemma InfClosed.finsetInf'_mem (hs : InfClosed s) (ht : t.Nonempty) :
    (∀ i ∈ t, f i ∈ s) → t.inf' ht f ∈ s :=
  inf'_induction _ _ hs

lemma InfClosed.finsetInf_mem [OrderTop α] (hs : InfClosed s) (ht : t.Nonempty) :
    (∀ i ∈ t, f i ∈ s) → t.inf f ∈ s :=
  inf'_eq_inf ht f ▸ hs.finsetInf'_mem ht
#align finset.inf_closed_of_inf_closed InfClosed.finsetInf_mem

structure IsSublattice (s : Set α) : Prop where
  supClosed : SupClosed s
  infClosed : InfClosed s

@[simp] lemma isSublattice_empty : IsSublattice (∅ : Set α) := ⟨supClosed_empty, infClosed_empty⟩
@[simp] lemma isSublattice_singleton : IsSublattice ({a} : Set α) :=
  ⟨supClosed_singleton, infClosed_singleton⟩

@[simp] lemma isSublattice_univ : IsSublattice (Set.univ : Set α) :=
  ⟨supClosed_univ, infClosed_univ⟩

lemma IsSublattice.inter (hs : IsSublattice s) (ht : IsSublattice t) : IsSublattice (s ∩ t) :=
  ⟨hs.1.inter ht.1, hs.2.inter ht.2⟩

lemma isSublattice_sInter (hS : ∀ s ∈ S, IsSublattice s) : IsSublattice (⋂₀ S) :=
  ⟨supClosed_sInter fun _s hs ↦ (hS _ hs).1, infClosed_sInter fun _s hs ↦ (hS _ hs).2⟩

lemma isSublattice_iInter (hf : ∀ i, IsSublattice (f i)) : IsSublattice (⋂ i, f i) :=
  ⟨supClosed_iInter fun _i ↦ (hf _).1, infClosed_iInter fun _i ↦ (hf _).2⟩

lemma IsSublattice.preimage [FunLike F β α] [LatticeHomClass F β α]
    (hs : IsSublattice s) (f : F) :
    IsSublattice (f ⁻¹' s) := ⟨hs.1.preimage _, hs.2.preimage _⟩

lemma IsSublattice.image [FunLike F α β] [LatticeHomClass F α β] (hs : IsSublattice s) (f : F) :
    IsSublattice (f '' s) := ⟨hs.1.image _, hs.2.image _⟩

lemma IsSublattice_range [FunLike F α β] [LatticeHomClass F α β] (f : F) :
    IsSublattice (Set.range f) :=
  ⟨supClosed_range _, infClosed_range _⟩

lemma IsSublattice.prod {t : Set β} (hs : IsSublattice s) (ht : IsSublattice t) :
    IsSublattice (s ×ˢ t) := ⟨hs.1.prod ht.1, hs.2.prod ht.2⟩

lemma isSublattice_pi {ι : Type*} {α : ι → Type*} [∀ i, Lattice (α i)] {s : Set ι}
    {t : ∀ i, Set (α i)} (ht : ∀ i ∈ s, IsSublattice (t i)) : IsSublattice (s.pi t) :=
  ⟨supClosed_pi fun _i hi ↦ (ht _ hi).1, infClosed_pi fun _i hi ↦ (ht _ hi).2⟩

@[simp] lemma supClosed_preimage_toDual {s : Set αᵒᵈ} :
    SupClosed (toDual ⁻¹' s) ↔ InfClosed s := Iff.rfl

@[simp] lemma infClosed_preimage_toDual {s : Set αᵒᵈ} :
    InfClosed (toDual ⁻¹' s) ↔ SupClosed s := Iff.rfl

@[simp] lemma supClosed_preimage_ofDual {s : Set α} :
    SupClosed (ofDual ⁻¹' s) ↔ InfClosed s := Iff.rfl

@[simp] lemma infClosed_preimage_ofDual {s : Set α} :
    InfClosed (ofDual ⁻¹' s) ↔ SupClosed s := Iff.rfl

@[simp] lemma isSublattice_preimage_toDual {s : Set αᵒᵈ} :
    IsSublattice (toDual ⁻¹' s) ↔ IsSublattice s := ⟨fun h ↦ ⟨h.2, h.1⟩, fun h ↦ ⟨h.2, h.1⟩⟩

@[simp] lemma isSublattice_preimage_ofDual :
    IsSublattice (ofDual ⁻¹' s) ↔ IsSublattice s := ⟨fun h ↦ ⟨h.2, h.1⟩, fun h ↦ ⟨h.2, h.1⟩⟩

alias ⟨_, InfClosed.dual⟩ := supClosed_preimage_ofDual
alias ⟨_, SupClosed.dual⟩ := infClosed_preimage_ofDual
alias ⟨_, IsSublattice.dual⟩ := isSublattice_preimage_ofDual
alias ⟨_, IsSublattice.of_dual⟩ := isSublattice_preimage_toDual

end Lattice

section LinearOrder
variable [LinearOrder α]

@[simp] protected lemma LinearOrder.supClosed (s : Set α) : SupClosed s :=
  fun a ha b hb ↦ by cases le_total a b <;> simp [*]

@[simp] protected lemma LinearOrder.infClosed (s : Set α) : InfClosed s :=
  fun a ha b hb ↦ by cases le_total a b <;> simp [*]

@[simp] protected lemma LinearOrder.isSublattice (s : Set α) : IsSublattice s :=
  ⟨LinearOrder.supClosed _, LinearOrder.infClosed _⟩

end LinearOrder

/-! ## Closure -/