def IsMinFilter : Prop :=
  ∀ᶠ x in l, f a ≤ f x
#align is_min_filter IsMinFilter

def IsMaxFilter : Prop :=
  ∀ᶠ x in l, f x ≤ f a
#align is_max_filter IsMaxFilter

def IsExtrFilter : Prop :=
  IsMinFilter f l a ∨ IsMaxFilter f l a
#align is_extr_filter IsExtrFilter

def IsMinOn :=
  IsMinFilter f (𝓟 s) a
#align is_min_on IsMinOn

def IsMaxOn :=
  IsMaxFilter f (𝓟 s) a
#align is_max_on IsMaxOn

def IsExtrOn : Prop :=
  IsExtrFilter f (𝓟 s) a
#align is_extr_on IsExtrOn