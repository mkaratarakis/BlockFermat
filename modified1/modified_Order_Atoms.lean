def IsAtom (a : α) : Prop :=
  a ≠ ⊥ ∧ ∀ b, b < a → b = ⊥
#align is_atom IsAtom

def IsCoatom [OrderTop α] (a : α) : Prop :=
  a ≠ ⊤ ∧ ∀ b, a < b → b = ⊤
#align is_coatom IsCoatom

def IsSimpleOrder.preorder {α} [LE α] [BoundedOrder α] [IsSimpleOrder α] : Preorder α
    where
  le := (· ≤ ·)
  le_refl a := by rcases eq_bot_or_eq_top a with (rfl | rfl) <;> simp
  le_trans a b c := by
    rcases eq_bot_or_eq_top a with (rfl | rfl)
    · simp
    · rcases eq_bot_or_eq_top b with (rfl | rfl)
      · rcases eq_bot_or_eq_top c with (rfl | rfl) <;> simp
      · simp
#align is_simple_order.preorder IsSimpleOrder.preorder

def IsSimpleOrder.linearOrder [DecidableEq α] : LinearOrder α :=
  { (inferInstance : PartialOrder α) with
    le_total := fun a b => by rcases eq_bot_or_eq_top a with (rfl | rfl) <;> simp
    decidableLE := fun a b =>
      if ha : a = ⊥ then isTrue (ha.le.trans bot_le)
      else
        if hb : b = ⊤ then isTrue (le_top.trans hb.ge)
        else
          isFalse fun H =>
            hb (top_unique (le_trans (top_le_iff.mpr (Or.resolve_left
              (eq_bot_or_eq_top a) ha)) H)) }
#align is_simple_order.linear_order IsSimpleOrder.linearOrder

def lattice {α} [DecidableEq α] [PartialOrder α] [BoundedOrder α] [IsSimpleOrder α] :
    Lattice α :=
  @LinearOrder.toLattice α IsSimpleOrder.linearOrder
#align is_simple_order.lattice IsSimpleOrder.lattice

def distribLattice : DistribLattice α :=
  { (inferInstance : Lattice α) with
    le_sup_inf := fun x y z => by rcases eq_bot_or_eq_top x with (rfl | rfl) <;> simp }
#align is_simple_order.distrib_lattice IsSimpleOrder.distribLattice

def equivBool {α} [DecidableEq α] [LE α] [BoundedOrder α] [IsSimpleOrder α] : α ≃ Bool
    where
  toFun x := x = ⊤
  invFun x := x.casesOn ⊥ ⊤
  left_inv x := by rcases eq_bot_or_eq_top x with (rfl | rfl) <;> simp [bot_ne_top]
  right_inv x := by cases x <;> simp [bot_ne_top]
#align is_simple_order.equiv_bool IsSimpleOrder.equivBool

def orderIsoBool : α ≃o Bool :=
  { equivBool with
    map_rel_iff' := @fun a b => by
      rcases eq_bot_or_eq_top a with (rfl | rfl)
      · simp [bot_ne_top]
      · rcases eq_bot_or_eq_top b with (rfl | rfl)
        · simp [bot_ne_top.symm, bot_ne_top, Bool.false_lt_true]
        · simp [bot_ne_top] }
#align is_simple_order.order_iso_bool IsSimpleOrder.orderIsoBool

def booleanAlgebra {α} [DecidableEq α] [Lattice α] [BoundedOrder α] [IsSimpleOrder α] :
    BooleanAlgebra α :=
  { inferInstanceAs (BoundedOrder α), IsSimpleOrder.distribLattice with
    compl := fun x => if x = ⊥ then ⊤ else ⊥
    sdiff := fun x y => if x = ⊤ ∧ y = ⊥ then ⊤ else ⊥
    sdiff_eq := fun x y => by
      rcases eq_bot_or_eq_top x with (rfl | rfl) <;> simp [bot_ne_top, SDiff.sdiff, compl]
    inf_compl_le_bot := fun x => by
      rcases eq_bot_or_eq_top x with (rfl | rfl)
      · simp
      · simp
    top_le_sup_compl := fun x => by rcases eq_bot_or_eq_top x with (rfl | rfl) <;> simp }
#align is_simple_order.boolean_algebra IsSimpleOrder.booleanAlgebra

def completeLattice : CompleteLattice α :=
  { (inferInstance : Lattice α),
    (inferInstance : BoundedOrder α) with
    sSup := fun s => if ⊤ ∈ s then ⊤ else ⊥
    sInf := fun s => if ⊥ ∈ s then ⊥ else ⊤
    le_sSup := fun s x h => by
      rcases eq_bot_or_eq_top x with (rfl | rfl)
      · exact bot_le
      · dsimp; rw [if_pos h]
    sSup_le := fun s x h => by
      rcases eq_bot_or_eq_top x with (rfl | rfl)
      · dsimp; rw [if_neg]
        intro con
        exact bot_ne_top (eq_top_iff.2 (h ⊤ con))
      · exact le_top
    sInf_le := fun s x h => by
      rcases eq_bot_or_eq_top x with (rfl | rfl)
      · dsimp; rw [if_pos h]
      · exact le_top
    le_sInf := fun s x h => by
      rcases eq_bot_or_eq_top x with (rfl | rfl)
      · exact bot_le
      · dsimp; rw [if_neg]
        intro con
        exact top_ne_bot (eq_bot_iff.2 (h ⊥ con)) }
#align is_simple_order.complete_lattice IsSimpleOrder.completeLattice

def completeBooleanAlgebra : CompleteBooleanAlgebra α :=
  { __ := IsSimpleOrder.completeLattice
    __ := IsSimpleOrder.booleanAlgebra
    iInf_sup_le_sup_sInf := fun x s => by
      rcases eq_bot_or_eq_top x with (rfl | rfl)
      · simp [bot_sup_eq, ← sInf_eq_iInf]
      · simp only [top_le_iff, top_sup_eq, iInf_top, le_sInf_iff, le_refl]
    inf_sSup_le_iSup_inf := fun x s => by
      rcases eq_bot_or_eq_top x with (rfl | rfl)
      · simp only [le_bot_iff, sSup_eq_bot, bot_inf_eq, iSup_bot, le_refl]
      · simp only [top_inf_eq, ← sSup_eq_iSup]
        exact le_rfl }
#align is_simple_order.complete_boolean_algebra IsSimpleOrder.completeBooleanAlgebra