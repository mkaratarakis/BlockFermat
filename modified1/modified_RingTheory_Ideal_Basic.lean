def Ideal (R : Type u) [Semiring R] :=
  Submodule R R
#align ideal Ideal

def span (s : Set α) : Ideal α :=
  Submodule.span α s
#align ideal.span Ideal.span

def ofRel (r : α → α → Prop) : Ideal α :=
  Submodule.span α { x | ∃ a b, r a b ∧ x + b = a }
#align ideal.of_rel Ideal.ofRel

def {I : Ideal α} : I.IsMaximal ↔ IsCoatom I :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩
#align ideal.is_maximal_def Ideal.isMaximal_def

def pi : Ideal (ι → α) where
  carrier := { x | ∀ i, x i ∈ I }
  zero_mem' _i := I.zero_mem
  add_mem' ha hb i := I.add_mem (ha i) (hb i)
  smul_mem' a _b hb i := I.mul_mem_left (a i) (hb i)
#align ideal.pi Ideal.pi

def equivFinTwo [DecidableEq (Ideal K)] : Ideal K ≃ Fin 2 where
  toFun := fun I ↦ if I = ⊥ then 0 else 1
  invFun := ![⊥, ⊤]
  left_inv := fun I ↦ by rcases eq_bot_or_top I with rfl | rfl <;> simp
  right_inv := fun i ↦ by fin_cases i <;> simp

instance : Finite (Ideal K) := let _i := Classical.decEq (Ideal K); ⟨equivFinTwo K⟩

/-- Ideals of a `DivisionSemiring` are a simple order. Thanks to the way abbreviations work,
this automatically gives an `IsSimpleModule K` instance. -/
instance isSimpleOrder : IsSimpleOrder (Ideal K) :=
  ⟨eq_bot_or_top⟩
#align ideal.is_simple_order Ideal.isSimpleOrder

def nonunits (α : Type u) [Monoid α] : Set α :=
  { a | ¬IsUnit a }
#align nonunits nonunits