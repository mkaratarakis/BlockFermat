def Disjoint (a b : α) : Prop :=
  ∀ ⦃x⦄, x ≤ a → x ≤ b → x ≤ ⊥
#align disjoint Disjoint

def Codisjoint (a b : α) : Prop :=
  ∀ ⦃x⦄, a ≤ x → b ≤ x → ⊤ ≤ x
#align codisjoint Codisjoint

def IsComplemented (a : α) : Prop :=
  ∃ b, IsCompl a b
#align is_complemented IsComplemented

def Complementeds (α : Type*) [Lattice α] [BoundedOrder α] : Type _ := {a : α // IsComplemented a}
#align complementeds Complementeds

structure IsCompl [PartialOrder α] [BoundedOrder α] (x y : α) : Prop where
  /-- If `x` and `y` are to be complementary in an order, they should be disjoint. -/
  protected disjoint : Disjoint x y
  /-- If `x` and `y` are to be complementary in an order, they should be codisjoint. -/
  protected codisjoint : Codisjoint x y
#align is_compl IsCompl