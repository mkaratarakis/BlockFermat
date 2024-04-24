def IsConj (a b : α) :=
  ∃ c : αˣ, SemiconjBy (↑c) a b
#align is_conj IsConj

def setoid (α : Type*) [Monoid α] : Setoid α where
  r := IsConj
  iseqv := ⟨IsConj.refl, IsConj.symm, IsConj.trans⟩
#align is_conj.setoid IsConj.setoid

def ConjClasses (α : Type*) [Monoid α] : Type _ :=
  Quotient (IsConj.setoid α)
#align conj_classes ConjClasses

def mk {α : Type*} [Monoid α] (a : α) : ConjClasses α := ⟦a⟧
#align conj_classes.mk ConjClasses.mk

def map (f : α →* β) : ConjClasses α → ConjClasses β :=
  Quotient.lift (ConjClasses.mk ∘ f) fun _ _ ab => mk_eq_mk_iff_isConj.2 (f.map_isConj ab)
#align conj_classes.map ConjClasses.map

def mkEquiv : α ≃ ConjClasses α :=
  ⟨ConjClasses.mk, Quotient.lift id fun (a : α) b => isConj_iff_eq.1, Quotient.lift_mk _ _, by
    rw [Function.RightInverse, Function.LeftInverse, forall_isConj]
    intro x
    rw [← quotient_mk_eq_mk, ← quotient_mk_eq_mk, Quotient.lift_mk, id]⟩
#align conj_classes.mk_equiv ConjClasses.mkEquiv

def conjugatesOf (a : α) : Set α :=
  { b | IsConj a b }
#align conjugates_of conjugatesOf

def carrier : ConjClasses α → Set α :=
  Quotient.lift conjugatesOf fun (_ : α) _ ab => IsConj.conjugatesOf_eq ab
#align conj_classes.carrier ConjClasses.carrier