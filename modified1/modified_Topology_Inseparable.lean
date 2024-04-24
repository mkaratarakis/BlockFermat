def : (x ~ᵢ y) ↔ 𝓝 x = 𝓝 y :=
  Iff.rfl
#align inseparable_def inseparable_def

def mk : X → SeparationQuotient X := Quotient.mk''
#align separation_quotient.mk SeparationQuotient.mk

def lift (f : X → α) (hf : ∀ x y, (x ~ᵢ y) → f x = f y) : SeparationQuotient X → α := fun x =>
  Quotient.liftOn' x f hf
#align separation_quotient.lift SeparationQuotient.lift

def lift₂ (f : X → Y → α) (hf : ∀ a b c d, (a ~ᵢ c) → (b ~ᵢ d) → f a b = f c d) :
    SeparationQuotient X → SeparationQuotient Y → α := fun x y => Quotient.liftOn₂' x y f hf
#align separation_quotient.lift₂ SeparationQuotient.lift₂