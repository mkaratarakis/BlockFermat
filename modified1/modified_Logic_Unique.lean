def because the typeclass search cannot
arbitrarily invent the `a : α` term. Nevertheless, these instances are all
equivalent by `Unique.Subsingleton.unique`.

See note [reducible non-instances]. -/
@[reducible]
def uniqueOfSubsingleton {α : Sort*} [Subsingleton α] (a : α) : Unique α where
  default := a
  uniq _ := Subsingleton.elim _ _
#align unique_of_subsingleton uniqueOfSubsingleton

def uniqueProp {p : Prop} (h : p) : Unique.{0} p where
  default := h
  uniq _ := rfl
#align unique_prop uniqueProp

def mk' (α : Sort u) [h₁ : Inhabited α] [Subsingleton α] : Unique α :=
  { h₁ with uniq := fun _ ↦ Subsingleton.elim _ _ }
#align unique.mk' Unique.mk'

def {β : α → Sort v} [∀ a, Inhabited (β a)] :
    @default (∀ a, β a) _ = fun a : α ↦ @default (β a) _ :=
  rfl
#align pi.default_def Pi.default_def

def Surjective.unique (f : α → β) (hf : Surjective f) [Unique.{u} α] : Unique β :=
  @Unique.mk' _ ⟨f default⟩ hf.subsingleton
#align function.surjective.unique Function.Surjective.unique

def Injective.unique [Inhabited α] [Subsingleton β] (hf : Injective f) : Unique α :=
  @Unique.mk' _ _ hf.subsingleton
#align function.injective.unique Function.Injective.unique

def Surjective.uniqueOfSurjectiveConst (α : Type*) {β : Type*} (b : β)
    (h : Function.Surjective (Function.const α b)) : Unique β :=
  @uniqueOfSubsingleton _ (subsingleton_of_forall_eq b <| h.forall.mpr fun _ ↦ rfl) b
#align function.surjective.unique_of_surjective_const Function.Surjective.uniqueOfSurjectiveConst

def uniqueElim [Unique ι] (x : α (default : ι)) (i : ι) : α i := by
  rw [Unique.eq_default i]
  exact x

@[simp]
theorem uniqueElim_default {_ : Unique ι} (x : α (default : ι)) : uniqueElim x (default : ι) = x :=
  rfl

@[simp]
theorem uniqueElim_const {_ : Unique ι} (x : β) (i : ι) : uniqueElim (α := fun _ ↦ β) x i = x :=
  rfl

end Pi

-- TODO: Mario turned this off as a simp lemma in Std, wanting to profile it.
attribute [local simp] eq_iff_true_of_subsingleton in
theorem Unique.bijective {A B} [Unique A] [Unique B] {f : A → B} : Function.Bijective f := by
  rw [Function.bijective_iff_has_inverse]
  refine' ⟨default, _, _⟩ <;> intro x <;> simp
#align unique.bijective Unique.bijective

structure Unique (α : Sort u) extends Inhabited α where
  /-- In a `Unique` type, every term is equal to the default element (from `Inhabited`). -/
  uniq : ∀ a : α, a = default
#align unique Unique