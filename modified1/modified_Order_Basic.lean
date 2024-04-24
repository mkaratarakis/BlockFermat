def := A_min_def, max_def := A_max_def,
      compare := A_compare, compare_eq_compareOfLessAndEq := A_compare_canonical, .. },
    { le := B_le, lt := B_lt,
      decidableLE := B_decidableLE, decidableEq := B_decidableEq, decidableLT := B_decidableLT
      min := B_min, max := B_max, min_def := B_min_def, max_def := B_max_def,
      compare := B_compare, compare_eq_compareOfLessAndEq := B_compare_canonical, .. } => by
    cases h
    obtain rfl : A_decidableLE = B_decidableLE := Subsingleton.elim _ _
    obtain rfl : A_decidableEq = B_decidableEq := Subsingleton.elim _ _
    obtain rfl : A_decidableLT = B_decidableLT := Subsingleton.elim _ _
    have : A_min = B_min := by
      funext a b
      exact (A_min_def _ _).trans (B_min_def _ _).symm
    cases this
    have : A_max = B_max := by
      funext a b
      exact (A_max_def _ _).trans (B_max_def _ _).symm
    cases this
    have : A_compare = B_compare := by
      funext a b
      exact (A_compare_canonical _ _).trans (B_compare_canonical _ _).symm
    congr
#align linear_order.to_partial_order_injective LinearOrder.toPartialOrder_injective

def Order.Preimage {α β} (f : α → β) (s : β → β → Prop) (x y : α) : Prop :=
  s (f x) (f y)
#align order.preimage Order.Preimage

def OrderDual (α : Type*) : Type _ :=
  α
#align order_dual OrderDual

def := fun a b ↦ show (max .. : α) = _ by rw [max_comm, max_def]; rfl
  max_def := fun a b ↦ show (min .. : α) = _ by rw [min_comm, min_def]; rfl
  decidableLE := (inferInstance : DecidableRel (fun a b : α ↦ b ≤ a))
  decidableLT := (inferInstance : DecidableRel (fun a b : α ↦ b < a))
#align order_dual.linear_order OrderDual.instLinearOrder

def {ι : Type u} {α : ι → Type v} [∀ i, HasCompl (α i)] (x : ∀ i, α i) :
    xᶜ = fun i ↦ (x i)ᶜ :=
  rfl
#align pi.compl_def Pi.compl_def

def {ι : Type u} {α : ι → Type v} [∀ i, LE (α i)] {x y : ∀ i, α i} :
    x ≤ y ↔ ∀ i, x i ≤ y i :=
  Iff.rfl
#align pi.le_def Pi.le_def

def {ι : Type u} {α : ι → Type v} [∀ i, Preorder (α i)] {x y : ∀ i, α i} :
    x < y ↔ x ≤ y ∧ ∃ i, x i < y i := by
  simp (config := { contextual := true }) [lt_iff_le_not_le, Pi.le_def]
#align pi.lt_def Pi.lt_def

def StrongLT [∀ i, LT (π i)] (a b : ∀ i, π i) : Prop :=
  ∀ i, a i < b i
#align strong_lt StrongLT

def {ι : Type u} {α : ι → Type v} [∀ i, SDiff (α i)] (x y : ∀ i, α i) :
    x \ y = fun i ↦ x i \ y i :=
  rfl
#align pi.sdiff_def Pi.sdiff_def

def Preorder.lift {α β} [Preorder β] (f : α → β) : Preorder α where
  le x y := f x ≤ f y
  le_refl _ := le_rfl
  le_trans _ _ _ := _root_.le_trans
  lt x y := f x < f y
  lt_iff_le_not_le _ _ := _root_.lt_iff_le_not_le
#align preorder.lift Preorder.lift

def PartialOrder.lift {α β} [PartialOrder β] (f : α → β) (inj : Injective f) : PartialOrder α :=
  { Preorder.lift f with le_antisymm := fun _ _ h₁ h₂ ↦ inj (h₁.antisymm h₂) }
#align partial_order.lift PartialOrder.lift

def LinearOrder.lift {α β} [LinearOrder β] [Sup α] [Inf α] (f : α → β) (inj : Injective f)
    (hsup : ∀ x y, f (x ⊔ y) = max (f x) (f y)) (hinf : ∀ x y, f (x ⊓ y) = min (f x) (f y)) :
    LinearOrder α :=
  letI instOrdα : Ord α := ⟨fun a b ↦ compare (f a) (f b)⟩
  letI decidableLE := fun x y ↦ (inferInstance : Decidable (f x ≤ f y))
  letI decidableLT := fun x y ↦ (inferInstance : Decidable (f x < f y))
  letI decidableEq := fun x y ↦ decidable_of_iff (f x = f y) inj.eq_iff
  { PartialOrder.lift f inj, instOrdα with
    le_total := fun x y ↦ le_total (f x) (f y)
    decidableLE := decidableLE
    decidableLT := decidableLT
    decidableEq := decidableEq
    min := (· ⊓ ·)
    max := (· ⊔ ·)
    min_def := by
      intros x y
      apply inj
      rw [apply_ite f]
      exact (hinf _ _).trans (min_def _ _)
    max_def := by
      intros x y
      apply inj
      rw [apply_ite f]
      exact (hsup _ _).trans (max_def _ _)
    compare_eq_compareOfLessAndEq := fun a b ↦
      compare_of_injective_eq_compareOfLessAndEq a b f inj }

/-- Transfer a `LinearOrder` on `β` to a `LinearOrder` on `α` using an injective
function `f : α → β`. This version autogenerates `min` and `max` fields. See `LinearOrder.lift`
for a version that takes `[Sup α]` and `[Inf α]`, then uses them as `max` and `min`. See
`LinearOrder.liftWithOrd'` for a version which does not auto-generate `compare` fields.
See note [reducible non-instances]. -/
@[reducible]
def LinearOrder.lift' {α β} [LinearOrder β] (f : α → β) (inj : Injective f) : LinearOrder α :=
  @LinearOrder.lift α β _ ⟨fun x y ↦ if f x ≤ f y then y else x⟩
    ⟨fun x y ↦ if f x ≤ f y then x else y⟩ f inj
    (fun _ _ ↦ (apply_ite f _ _ _).trans (max_def _ _).symm) fun _ _ ↦
    (apply_ite f _ _ _).trans (min_def _ _).symm
#align linear_order.lift' LinearOrder.lift'

def LinearOrder.liftWithOrd {α β} [LinearOrder β] [Sup α] [Inf α] [Ord α] (f : α → β)
    (inj : Injective f) (hsup : ∀ x y, f (x ⊔ y) = max (f x) (f y))
    (hinf : ∀ x y, f (x ⊓ y) = min (f x) (f y))
    (compare_f : ∀ a b : α, compare a b = compare (f a) (f b)) : LinearOrder α :=
  letI decidableLE := fun x y ↦ (inferInstance : Decidable (f x ≤ f y))
  letI decidableLT := fun x y ↦ (inferInstance : Decidable (f x < f y))
  letI decidableEq := fun x y ↦ decidable_of_iff (f x = f y) inj.eq_iff
  { PartialOrder.lift f inj with
    le_total := fun x y ↦ le_total (f x) (f y)
    decidableLE := decidableLE
    decidableLT := decidableLT
    decidableEq := decidableEq
    min := (· ⊓ ·)
    max := (· ⊔ ·)
    min_def := by
      intros x y
      apply inj
      rw [apply_ite f]
      exact (hinf _ _).trans (min_def _ _)
    max_def := by
      intros x y
      apply inj
      rw [apply_ite f]
      exact (hsup _ _).trans (max_def _ _)
    compare_eq_compareOfLessAndEq := fun a b ↦
      (compare_f a b).trans <| compare_of_injective_eq_compareOfLessAndEq a b f inj }

/-- Transfer a `LinearOrder` on `β` to a `LinearOrder` on `α` using an injective
function `f : α → β`. This version auto-generates `min` and `max` fields. It also takes `[Ord α]`
as an argument and uses them for `compare` fields. See `LinearOrder.lift` for a version that
autogenerates `compare` fields, and `LinearOrder.liftWithOrd` for one that doesn't auto-generate
`min` and `max` fields. fields. See note [reducible non-instances]. -/
@[reducible]
def LinearOrder.liftWithOrd' {α β} [LinearOrder β] [Ord α] (f : α → β)
    (inj : Injective f)
    (compare_f : ∀ a b : α, compare a b = compare (f a) (f b)) : LinearOrder α :=
  @LinearOrder.liftWithOrd α β _ ⟨fun x y ↦ if f x ≤ f y then y else x⟩
    ⟨fun x y ↦ if f x ≤ f y then x else y⟩ _ f inj
    (fun _ _ ↦ (apply_ite f _ _ _).trans (max_def _ _).symm)
    (fun _ _ ↦ (apply_ite f _ _ _).trans (min_def _ _).symm)
    compare_f

/-! ### Subtype of an order -/

def [LE α] [LE β] {x y : α × β} : x ≤ y ↔ x.1 ≤ y.1 ∧ x.2 ≤ y.2 :=
  Iff.rfl
#align prod.le_def Prod.le_def

def AsLinearOrder (α : Type u) :=
  α
#align as_linear_order AsLinearOrder