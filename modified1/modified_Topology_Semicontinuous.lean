def LowerSemicontinuousWithinAt (f : α → β) (s : Set α) (x : α) :=
  ∀ y < f x, ∀ᶠ x' in 𝓝[s] x, y < f x'
#align lower_semicontinuous_within_at LowerSemicontinuousWithinAt

def LowerSemicontinuousOn (f : α → β) (s : Set α) :=
  ∀ x ∈ s, LowerSemicontinuousWithinAt f s x
#align lower_semicontinuous_on LowerSemicontinuousOn

def LowerSemicontinuousAt (f : α → β) (x : α) :=
  ∀ y < f x, ∀ᶠ x' in 𝓝 x, y < f x'
#align lower_semicontinuous_at LowerSemicontinuousAt

def LowerSemicontinuous (f : α → β) :=
  ∀ x, LowerSemicontinuousAt f x
#align lower_semicontinuous LowerSemicontinuous

def UpperSemicontinuousWithinAt (f : α → β) (s : Set α) (x : α) :=
  ∀ y, f x < y → ∀ᶠ x' in 𝓝[s] x, f x' < y
#align upper_semicontinuous_within_at UpperSemicontinuousWithinAt

def UpperSemicontinuousOn (f : α → β) (s : Set α) :=
  ∀ x ∈ s, UpperSemicontinuousWithinAt f s x
#align upper_semicontinuous_on UpperSemicontinuousOn

def UpperSemicontinuousAt (f : α → β) (x : α) :=
  ∀ y, f x < y → ∀ᶠ x' in 𝓝 x, f x' < y
#align upper_semicontinuous_at UpperSemicontinuousAt

def UpperSemicontinuous (f : α → β) :=
  ∀ x, UpperSemicontinuousAt f x
#align upper_semicontinuous UpperSemicontinuous