def IsUpperSet (s : Set α) : Prop :=
  ∀ ⦃a b : α⦄, a ≤ b → a ∈ s → b ∈ s
#align is_upper_set IsUpperSet

def IsLowerSet (s : Set α) : Prop :=
  ∀ ⦃a b : α⦄, b ≤ a → a ∈ s → b ∈ s
#align is_lower_set IsLowerSet

def Simps.coe (s : UpperSet α) : Set α := s

initialize_simps_projections UpperSet (carrier → coe)

@[ext]
theorem ext {s t : UpperSet α} : (s : Set α) = t → s = t :=
  SetLike.ext'
#align upper_set.ext UpperSet.ext

def Simps.coe (s : LowerSet α) : Set α := s

initialize_simps_projections LowerSet (carrier → coe)

@[ext]
theorem ext {s t : LowerSet α} : (s : Set α) = t → s = t :=
  SetLike.ext'
#align lower_set.ext LowerSet.ext

def UpperSet.compl (s : UpperSet α) : LowerSet α :=
  ⟨sᶜ, s.upper.compl⟩
#align upper_set.compl UpperSet.compl

def LowerSet.compl (s : LowerSet α) : UpperSet α :=
  ⟨sᶜ, s.lower.compl⟩
#align lower_set.compl LowerSet.compl

def upperSetIsoLowerSet : UpperSet α ≃o LowerSet α
    where
  toFun := UpperSet.compl
  invFun := LowerSet.compl
  left_inv := UpperSet.compl_compl
  right_inv := LowerSet.compl_compl
  map_rel_iff' := UpperSet.compl_le_compl
#align upper_set_iso_lower_set upperSetIsoLowerSet

def map (f : α ≃o β) : UpperSet α ≃o UpperSet β where
  toFun s := ⟨f '' s, s.upper.image f⟩
  invFun t := ⟨f ⁻¹' t, t.upper.preimage f.monotone⟩
  left_inv _ := ext <| f.preimage_image _
  right_inv _ := ext <| f.image_preimage _
  map_rel_iff' := image_subset_image_iff f.injective
#align upper_set.map UpperSet.map

def map (f : α ≃o β) : LowerSet α ≃o LowerSet β where
  toFun s := ⟨f '' s, s.lower.image f⟩
  invFun t := ⟨f ⁻¹' t, t.lower.preimage f.monotone⟩
  left_inv _ := SetLike.coe_injective <| f.preimage_image _
  right_inv _ := SetLike.coe_injective <| f.image_preimage _
  map_rel_iff' := image_subset_image_iff f.injective
#align lower_set.map LowerSet.map

def Ici (a : α) : UpperSet α :=
  ⟨Ici a, isUpperSet_Ici a⟩
#align upper_set.Ici UpperSet.Ici

def Ioi (a : α) : UpperSet α :=
  ⟨Ioi a, isUpperSet_Ioi a⟩
#align upper_set.Ioi UpperSet.Ioi

def Iic (a : α) : LowerSet α :=
  ⟨Iic a, isLowerSet_Iic a⟩
#align lower_set.Iic LowerSet.Iic

def Iio (a : α) : LowerSet α :=
  ⟨Iio a, isLowerSet_Iio a⟩
#align lower_set.Iio LowerSet.Iio

def upperClosure (s : Set α) : UpperSet α :=
  ⟨{ x | ∃ a ∈ s, a ≤ x }, fun _ _ hle h => h.imp fun _x hx => ⟨hx.1, hx.2.trans hle⟩⟩
#align upper_closure upperClosure

def lowerClosure (s : Set α) : LowerSet α :=
  ⟨{ x | ∃ a ∈ s, x ≤ a }, fun _ _ hle h => h.imp fun _x hx => ⟨hx.1, hle.trans hx.2⟩⟩
#align lower_closure lowerClosure

def giUpperClosureCoe :
    GaloisInsertion (toDual ∘ upperClosure : Set α → (UpperSet α)ᵒᵈ) ((↑) ∘ ofDual) where
  choice s hs := toDual (⟨s, fun a _b hab ha => hs ⟨a, ha, hab⟩⟩ : UpperSet α)
  gc := gc_upperClosure_coe
  le_l_u _ := subset_upperClosure
  choice_eq _s hs := ofDual.injective <| SetLike.coe_injective <| subset_upperClosure.antisymm hs
#align gi_upper_closure_coe giUpperClosureCoe

def giLowerClosureCoe : GaloisInsertion (lowerClosure : Set α → LowerSet α) (↑) where
  choice s hs := ⟨s, fun a _b hba ha => hs ⟨a, ha, hba⟩⟩
  gc := gc_lowerClosure_coe
  le_l_u _ := subset_lowerClosure
  choice_eq _s hs := SetLike.coe_injective <| subset_lowerClosure.antisymm hs
#align gi_lower_closure_coe giLowerClosureCoe

def sdiff (s : LowerSet α) (t : Set α) : LowerSet α where
  carrier := s \ upperClosure t
  lower' := s.lower.sdiff_of_isUpperSet (upperClosure t).upper

/-- The biggest lower subset of a lower set `s` not containing an element `a`. -/
def erase (s : LowerSet α) (a : α) : LowerSet α where
  carrier := s \ UpperSet.Ici a
  lower' := s.lower.sdiff_of_isUpperSet (UpperSet.Ici a).upper

@[simp, norm_cast]
lemma coe_sdiff (s : LowerSet α) (t : Set α) : s.sdiff t = (s : Set α) \ upperClosure t := rfl

@[simp, norm_cast]
lemma coe_erase (s : LowerSet α) (a : α) : s.erase a = (s : Set α) \ UpperSet.Ici a := rfl

@[simp] lemma sdiff_singleton (s : LowerSet α) (a : α) : s.sdiff {a} = s.erase a := by
  simp [sdiff, erase]

lemma sdiff_le_left : s.sdiff t ≤ s := diff_subset _ _
lemma erase_le : s.erase a ≤ s := diff_subset _ _

@[simp] protected lemma sdiff_eq_left : s.sdiff t = s ↔ Disjoint ↑s t := by
  simp [← SetLike.coe_set_eq]

@[simp] lemma erase_eq : s.erase a = s ↔ a ∉ s := by rw [← sdiff_singleton]; simp [-sdiff_singleton]

@[simp] lemma sdiff_lt_left : s.sdiff t < s ↔ ¬ Disjoint ↑s t :=
  sdiff_le_left.lt_iff_ne.trans LowerSet.sdiff_eq_left.not

@[simp] lemma erase_lt : s.erase a < s ↔ a ∈ s := erase_le.lt_iff_ne.trans erase_eq.not_left

@[simp] protected lemma sdiff_idem (s : LowerSet α) (t : Set α) : (s.sdiff t).sdiff t = s.sdiff t :=
  SetLike.coe_injective sdiff_idem

@[simp] lemma erase_idem (s : LowerSet α) (a : α) : (s.erase a).erase a = s.erase a :=
  SetLike.coe_injective sdiff_idem

lemma sdiff_sup_lowerClosure (hts : t ⊆ s) (hst : ∀ b ∈ s, ∀ c ∈ t, c ≤ b → b ∈ t) :
    s.sdiff t ⊔ lowerClosure t = s := by
  refine' le_antisymm (sup_le sdiff_le_left <| lowerClosure_le.2 hts) fun a ha ↦ _
  obtain hat | hat := em (a ∈ t)
  · exact subset_union_right _ _ (subset_lowerClosure hat)
  · refine subset_union_left _ _ ⟨ha, ?_⟩
    rintro ⟨b, hb, hba⟩
    exact hat <| hst _ ha _ hb hba

lemma lowerClosure_sup_sdiff (hts : t ⊆ s) (hst : ∀ b ∈ s, ∀ c ∈ t, c ≤ b → b ∈ t) :
    lowerClosure t ⊔ s.sdiff t = s := by rw [sup_comm, sdiff_sup_lowerClosure hts hst]

lemma erase_sup_Iic (ha : a ∈ s) (has : ∀ b ∈ s, a ≤ b → b = a) : s.erase a ⊔ Iic a = s := by
  rw [← lowerClosure_singleton, ← sdiff_singleton, sdiff_sup_lowerClosure] <;> simpa

lemma Iic_sup_erase (ha : a ∈ s) (has : ∀ b ∈ s, a ≤ b → b = a) : Iic a ⊔ s.erase a = s := by
  rw [sup_comm, erase_sup_Iic ha has]

end LowerSet

namespace UpperSet
variable [Preorder α] {s : UpperSet α} {t : Set α} {a : α}

/-- The biggest upper subset of a upper set `s` disjoint from a set `t`. -/
def sdiff (s : UpperSet α) (t : Set α) : UpperSet α where
  carrier := s \ lowerClosure t
  upper' := s.upper.sdiff_of_isLowerSet (lowerClosure t).lower

/-- The biggest upper subset of a upper set `s` not containing an element `a`. -/
def erase (s : UpperSet α) (a : α) : UpperSet α where
  carrier := s \ LowerSet.Iic a
  upper' := s.upper.sdiff_of_isLowerSet (LowerSet.Iic a).lower

@[simp, norm_cast]
lemma coe_sdiff (s : UpperSet α) (t : Set α) : s.sdiff t = (s : Set α) \ lowerClosure t := rfl

@[simp, norm_cast]
lemma coe_erase (s : UpperSet α) (a : α) : s.erase a = (s : Set α) \ LowerSet.Iic a := rfl

@[simp] lemma sdiff_singleton (s : UpperSet α) (a : α) : s.sdiff {a} = s.erase a := by
  simp [sdiff, erase]

lemma le_sdiff_left : s ≤ s.sdiff t := diff_subset _ _
lemma le_erase : s ≤ s.erase a := diff_subset _ _

@[simp] protected lemma sdiff_eq_left : s.sdiff t = s ↔ Disjoint ↑s t := by
  simp [← SetLike.coe_set_eq]

@[simp] lemma erase_eq : s.erase a = s ↔ a ∉ s := by rw [← sdiff_singleton]; simp [-sdiff_singleton]

@[simp] lemma lt_sdiff_left : s < s.sdiff t ↔ ¬ Disjoint ↑s t :=
  le_sdiff_left.gt_iff_ne.trans UpperSet.sdiff_eq_left.not

@[simp] lemma lt_erase : s < s.erase a ↔ a ∈ s := le_erase.gt_iff_ne.trans erase_eq.not_left

@[simp] protected lemma sdiff_idem (s : UpperSet α) (t : Set α) : (s.sdiff t).sdiff t = s.sdiff t :=
  SetLike.coe_injective sdiff_idem

@[simp] lemma erase_idem (s : UpperSet α) (a : α) : (s.erase a).erase a = s.erase a :=
  SetLike.coe_injective sdiff_idem

lemma sdiff_inf_upperClosure (hts : t ⊆ s) (hst : ∀ b ∈ s, ∀ c ∈ t, b ≤ c → b ∈ t) :
    s.sdiff t ⊓ upperClosure t = s := by
  refine' ge_antisymm (le_inf le_sdiff_left <| le_upperClosure.2 hts) fun a ha ↦ _
  obtain hat | hat := em (a ∈ t)
  · exact subset_union_right _ _ (subset_upperClosure hat)
  · refine subset_union_left _ _ ⟨ha, ?_⟩
    rintro ⟨b, hb, hab⟩
    exact hat <| hst _ ha _ hb hab

lemma upperClosure_inf_sdiff (hts : t ⊆ s) (hst : ∀ b ∈ s, ∀ c ∈ t, b ≤ c → b ∈ t) :
    upperClosure t ⊓ s.sdiff t = s := by rw [inf_comm, sdiff_inf_upperClosure hts hst]

lemma erase_inf_Ici (ha : a ∈ s) (has : ∀ b ∈ s, b ≤ a → b = a) : s.erase a ⊓ Ici a = s := by
  rw [← upperClosure_singleton, ← sdiff_singleton, sdiff_inf_upperClosure] <;> simpa

lemma Ici_inf_erase (ha : a ∈ s) (has : ∀ b ∈ s, b ≤ a → b = a) : Ici a ⊓ s.erase a = s := by
  rw [inf_comm, erase_inf_Ici ha has]

end UpperSet

/-! ### Product -/

def prod : UpperSet (α × β) :=
  ⟨s ×ˢ t, s.2.prod t.2⟩
#align upper_set.prod UpperSet.prod

def prod : LowerSet (α × β) := ⟨s ×ˢ t, s.2.prod t.2⟩
#align lower_set.prod LowerSet.prod

structure on antichains. Order equivalence between upper/lower sets and antichains.
-/

open Function OrderDual Set

variable {α β γ : Type*} {ι : Sort*} {κ : ι → Sort*}

/-! ### Unbundled upper/lower sets -/

structure UpperSet (α : Type*) [LE α] where
  /-- The carrier of an `UpperSet`. -/
  carrier : Set α
  /-- The carrier of an `UpperSet` is an upper set. -/
  upper' : IsUpperSet carrier
#align upper_set UpperSet

structure LowerSet (α : Type*) [LE α] where
  /-- The carrier of a `LowerSet`. -/
  carrier : Set α
  /-- The carrier of a `LowerSet` is a lower set. -/
  lower' : IsLowerSet carrier
#align lower_set LowerSet