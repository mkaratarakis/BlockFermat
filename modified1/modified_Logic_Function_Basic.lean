def eval {β : α → Sort*} (x : α) (f : ∀ x, β x) : β x := f x
#align function.eval Function.eval

def {y : β} : (fun _ : α ↦ y) = const α y :=
  rfl
#align function.const_def Function.const_def

def : @id α = fun x ↦ x :=
  rfl
#align function.id_def Function.id_def

def Injective.decidableEq [DecidableEq β] (I : Injective f) : DecidableEq α :=
  fun _ _ ↦ decidable_of_iff _ I.eq_iff
#align function.injective.decidable_eq Function.Injective.decidableEq

def IsPartialInv {α β} (f : α → β) (g : β → Option α) : Prop :=
  ∀ x y, g y = some x ↔ f x = y
#align function.is_partial_inv Function.IsPartialInv

def partialInv {α β} (f : α → β) (b : β) : Option α :=
  if h : ∃ a, f a = b then some (Classical.choose h) else none
#align function.partial_inv Function.partialInv

def invFun {α : Sort u} {β} [Nonempty α] (f : α → β) : β → α :=
  fun y ↦ if h : (∃ x, f x = y) then h.choose else Classical.arbitrary α
#align function.inv_fun Function.invFun

def surjInv {f : α → β} (h : Surjective f) (b : β) : α :=
  Classical.choose (h b)
#align function.surj_inv Function.surjInv

def update (f : ∀ a, β a) (a' : α) (v : β a') (a : α) : β a :=
  if h : a = a' then Eq.ndrec v h.symm else f a
#align function.update Function.update

def extend (f : α → β) (g : α → γ) (j : β → γ) : β → γ := fun b ↦
  if h : ∃ a, f a = b then g (Classical.choose h) else j b
#align function.extend Function.extend

def FactorsThrough (g : α → γ) (f : α → β) : Prop :=
  ∀ ⦃a b⦄, f a = f b → g a = g b
#align function.factors_through Function.FactorsThrough

def (f : α → β) (g : α → γ) (e' : β → γ) (b : β) [Decidable (∃ a, f a = b)] :
    extend f g e' b = if h : ∃ a, f a = b then g (Classical.choose h) else e' b := by
  unfold extend
  congr
#align function.extend_def Function.extend_def

def {α β γ} (f : α → β → γ) : uncurry f = fun p ↦ f p.1 p.2 :=
  rfl
#align function.uncurry_def Function.uncurry_def

def bicompl (f : γ → δ → ε) (g : α → γ) (h : β → δ) (a b) :=
  f (g a) (h b)
#align function.bicompl Function.bicompl

def bicompr (f : γ → δ) (g : α → β → γ) (a b) :=
  f (g a b)
#align function.bicompr Function.bicompr

def Involutive {α} (f : α → α) : Prop :=
  ∀ x, f (f x) = x
#align function.involutive Function.Involutive

def Injective2 {α β γ} (f : α → β → γ) : Prop :=
  ∀ ⦃a₁ a₂ b₁ b₂⦄, f a₁ b₁ = f a₂ b₂ → a₁ = a₂ ∧ b₁ = b₂
#align function.injective2 Function.Injective2

def sometimes {α β} [Nonempty β] (f : α → β) : β :=
  if h : Nonempty α then f (Classical.choice h) else Classical.choice ‹_›
#align function.sometimes Function.sometimes

def Set.piecewise {α : Type u} {β : α → Sort v} (s : Set α) (f g : ∀ i, β i)
    [∀ j, Decidable (j ∈ s)] : ∀ i, β i :=
  fun i ↦ if i ∈ s then f i else g i
#align set.piecewise Set.piecewise

def Set.SeparatesPoints {α β : Type*} (A : Set (α → β)) : Prop :=
  ∀ ⦃x y : α⦄, x ≠ y → ∃ f ∈ A, (f x : β) ≠ f y
#align set.separates_points Set.SeparatesPoints