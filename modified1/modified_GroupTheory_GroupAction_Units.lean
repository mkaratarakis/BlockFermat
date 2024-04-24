def [Monoid M] [SMul M α] (m : Mˣ) (a : α) : m • a = (m : M) • a :=
  rfl
#align units.smul_def Units.smul_def

def AddUnits.vadd_def

@[to_additive, simp]
theorem smul_mk_apply {M α : Type*} [Monoid M] [SMul M α] (m n : M) (h₁) (h₂) (a : α) :
    (⟨m, n, h₁, h₂⟩ : Mˣ) • a = m • a :=
  rfl

@[simp]
theorem smul_isUnit [Monoid M] [SMul M α] {m : M} (hm : IsUnit m) (a : α) :
    hm.unit • a = m • a :=
  rfl
#align units.smul_is_unit Units.smul_isUnit