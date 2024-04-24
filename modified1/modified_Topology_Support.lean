def mulTSupport (f : X → α) : Set X := closure (mulSupport f)
#align mul_tsupport mulTSupport

def HasCompactMulSupport (f : α → β) : Prop :=
  IsCompact (mulTSupport f)
#align has_compact_mul_support HasCompactMulSupport

def : HasCompactMulSupport f ↔ IsCompact (closure (mulSupport f)) := by
  rfl
#align has_compact_mul_support_def hasCompactMulSupport_def

def hasCompactSupport_def

@[to_additive]
theorem exists_compact_iff_hasCompactMulSupport [R1Space α] :
    (∃ K : Set α, IsCompact K ∧ ∀ x, x ∉ K → f x = 1) ↔ HasCompactMulSupport f := by
  simp_rw [← nmem_mulSupport, ← mem_compl_iff, ← subset_def, compl_subset_compl,
    hasCompactMulSupport_def, exists_isCompact_superset_iff]
#align exists_compact_iff_has_compact_mul_support exists_compact_iff_hasCompactMulSupport