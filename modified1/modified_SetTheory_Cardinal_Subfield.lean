def operate : (Σ n, Operands s n → closure s) → closure s
  | ⟨.inl 0, f⟩ => f false + f true
  | ⟨.inl 1, f⟩ => f false * f true
  | ⟨.inl 2, f⟩ => - f ()
  | ⟨.inl 3, f⟩ => (f ())⁻¹
  | ⟨.inl 4, _⟩ => 0
  | ⟨.inl 5, _⟩ => 1
  | ⟨.inr a, _⟩ => ⟨a, subset_closure a.prop⟩

private def rangeOfWType : Subfield (closure s) where
  carrier := Set.range (WType.elim _ <| operate s)
  add_mem' := by rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩; exact ⟨WType.mk (.inl 0) (Bool.rec x y), by rfl⟩
  mul_mem' := by rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩; exact ⟨WType.mk (.inl 1) (Bool.rec x y), by rfl⟩
  neg_mem' := by rintro _ ⟨x, rfl⟩; exact ⟨WType.mk (.inl 2) fun _ ↦ x, rfl⟩
  inv_mem' := by rintro _ ⟨x, rfl⟩; exact ⟨WType.mk (.inl 3) fun _ ↦ x, rfl⟩
  zero_mem' := ⟨WType.mk (.inl 4) Empty.rec, rfl⟩
  one_mem' := ⟨WType.mk (.inl 5) Empty.rec, rfl⟩

private lemma rangeOfWType_eq_top : rangeOfWType s = ⊤ := top_le_iff.mp fun a _ ↦ by
  rw [← SetLike.mem_coe, ← Subtype.val_injective.mem_set_image]
  change ↑a ∈ map (closure s).subtype _
  refine closure_le.mpr (fun a ha ↦ ?_) a.prop
  exact ⟨⟨a, subset_closure ha⟩, ⟨WType.mk (.inr ⟨a, ha⟩) Empty.rec, rfl⟩, rfl⟩

private lemma surjective_ofWType : Function.Surjective (WType.elim _ <| operate s) := by
  rw [← Set.range_iff_surjective]
  exact SetLike.coe_set_eq.mpr (rangeOfWType_eq_top s)

open Cardinal

lemma cardinal_mk_closure_le_max : #(closure s) ≤ max #s ℵ₀ :=