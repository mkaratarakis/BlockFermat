def Monotone (f : α → β) : Prop :=
  ∀ ⦃a b⦄, a ≤ b → f a ≤ f b
#align monotone Monotone

def Antitone (f : α → β) : Prop :=
  ∀ ⦃a b⦄, a ≤ b → f b ≤ f a
#align antitone Antitone

def MonotoneOn (f : α → β) (s : Set α) : Prop :=
  ∀ ⦃a⦄ (_ : a ∈ s) ⦃b⦄ (_ : b ∈ s), a ≤ b → f a ≤ f b
#align monotone_on MonotoneOn

def AntitoneOn (f : α → β) (s : Set α) : Prop :=
  ∀ ⦃a⦄ (_ : a ∈ s) ⦃b⦄ (_ : b ∈ s), a ≤ b → f b ≤ f a
#align antitone_on AntitoneOn

def StrictMono (f : α → β) : Prop :=
  ∀ ⦃a b⦄, a < b → f a < f b
#align strict_mono StrictMono

def StrictAnti (f : α → β) : Prop :=
  ∀ ⦃a b⦄, a < b → f b < f a
#align strict_anti StrictAnti

def StrictMonoOn (f : α → β) (s : Set α) : Prop :=
  ∀ ⦃a⦄ (_ : a ∈ s) ⦃b⦄ (_ : b ∈ s), a < b → f a < f b
#align strict_mono_on StrictMonoOn

def StrictAntiOn (f : α → β) (s : Set α) : Prop :=
  ∀ ⦃a⦄ (_ : a ∈ s) ⦃b⦄ (_ : b ∈ s), a < b → f b < f a
#align strict_anti_on StrictAntiOn