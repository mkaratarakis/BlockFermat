def (r : R) (x : s) : r • x = ⟨r • x, smul_mem r x.2⟩ :=
  rfl
#align set_like.smul_def SetLike.smul_def

def SetLike.vadd_def

@[simp]
theorem forall_smul_mem_iff {R M S : Type*} [Monoid R] [MulAction R M] [SetLike S M]
    [SMulMemClass S R M] {N : S} {x : M} : (∀ a : R, a • x ∈ N) ↔ x ∈ N :=
  ⟨fun h => by simpa using h 1, fun h a => SMulMemClass.smul_mem a h⟩
#align set_like.forall_smul_mem_iff SetLike.forall_smul_mem_iff

def copy (p : SubMulAction R M) (s : Set M) (hs : s = ↑p) : SubMulAction R M
    where
  carrier := s
  smul_mem' := hs.symm ▸ p.smul_mem'
#align sub_mul_action.copy SubMulAction.copy

def subtype : p →[R] M := by refine' { toFun := Subtype.val.. }; simp [val_smul]
#align sub_mul_action.subtype SubMulAction.subtype

def subtype : S' →[R] M where
  toFun := Subtype.val; map_smul' _ _ := rfl
#align sub_mul_action.smul_mem_class.subtype SubMulAction.SMulMemClass.subtype

structure SubMulAction (R : Type u) (M : Type v) [SMul R M] : Type v where
  /-- The underlying set of a `SubMulAction`. -/
  carrier : Set M
  /-- The carrier set is closed under scalar multiplication. -/
  smul_mem' : ∀ (c : R) {x : M}, x ∈ carrier → c • x ∈ carrier
#align sub_mul_action SubMulAction

structure eta
#noalign sub_mul_action.coe_mk