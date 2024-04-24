def upperBounds (s : Set α) : Set α :=
  { x | ∀ ⦃a⦄, a ∈ s → a ≤ x }
#align upper_bounds upperBounds

def lowerBounds (s : Set α) : Set α :=
  { x | ∀ ⦃a⦄, a ∈ s → x ≤ a }
#align lower_bounds lowerBounds

def BddAbove (s : Set α) :=
  (upperBounds s).Nonempty
#align bdd_above BddAbove

def BddBelow (s : Set α) :=
  (lowerBounds s).Nonempty
#align bdd_below BddBelow

def IsLeast (s : Set α) (a : α) : Prop :=
  a ∈ s ∧ a ∈ lowerBounds s
#align is_least IsLeast

def IsGreatest (s : Set α) (a : α) : Prop :=
  a ∈ s ∧ a ∈ upperBounds s
#align is_greatest IsGreatest

def IsLUB (s : Set α) : α → Prop :=
  IsLeast (upperBounds s)
#align is_lub IsLUB

def IsGLB (s : Set α) : α → Prop :=
  IsGreatest (lowerBounds s)
#align is_glb IsGLB

def : BddAbove s ↔ ∃ x, ∀ y ∈ s, y ≤ x :=
  Iff.rfl
#align bdd_above_def bddAbove_def

def : BddBelow s ↔ ∃ x, ∀ y ∈ s, x ≤ y :=
  Iff.rfl
#align bdd_below_def bddBelow_def

def IsLeast.orderBot (h : IsLeast s a) :
    OrderBot s where
  bot := ⟨a, h.1⟩
  bot_le := Subtype.forall.2 h.2
#align is_least.order_bot IsLeast.orderBot

def IsGreatest.orderTop (h : IsGreatest s a) :
    OrderTop s where
  top := ⟨a, h.1⟩
  le_top := Subtype.forall.2 h.2
#align is_greatest.order_top IsGreatest.orderTop

def ScottContinuous (f : α → β) : Prop :=
  ∀ ⦃d : Set α⦄, d.Nonempty → DirectedOn (· ≤ ·) d → ∀ ⦃a⦄, IsLUB d a → IsLUB (f '' d) (f a)
#align scott_continuous ScottContinuous

structure and uses
`¬(y ≤ x)`. A version for linear orders is called `not_bddAbove_iff`. -/
theorem not_bddAbove_iff' : ¬BddAbove s ↔ ∀ x, ∃ y ∈ s, ¬y ≤ x := by
  simp [BddAbove, upperBounds, Set.Nonempty]
#align not_bdd_above_iff' not_bddAbove_iff'

structure and uses
`¬(x ≤ y)`. A version for linear orders is called `not_bddBelow_iff`. -/
theorem not_bddBelow_iff' : ¬BddBelow s ↔ ∀ x, ∃ y ∈ s, ¬x ≤ y :=
  @not_bddAbove_iff' αᵒᵈ _ _
#align not_bdd_below_iff' not_bddBelow_iff'