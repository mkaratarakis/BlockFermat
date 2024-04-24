def hidden {α : Sort*} {a : α} := a
#align hidden hidden

def Function.swap₂ {κ₁ : ι₁ → Sort*} {κ₂ : ι₂ → Sort*}
    {φ : ∀ i₁, κ₁ i₁ → ∀ i₂, κ₂ i₂ → Sort*} (f : ∀ i₁ j₁ i₂ j₂, φ i₁ j₁ i₂ j₂)
    (i₂ j₂ i₁ j₁) : φ i₁ j₁ i₂ j₂ := f i₁ j₁ i₂ j₂
#align function.swap₂ Function.swap₂

def autoParam'.out {α : Sort*} {n : Name} (x : autoParam' α n) : α := x

-- /-- If `x : α := d` then `x.out : α`. These are definitionally equal, but this can
-- nevertheless be useful for various reasons, e.g. to apply further projection notation or in an
-- argument to `simp`. -/
-- def optParam.out {α : Sort*} {d : α} (x : α := d) : α := x

end Miscellany

open Function

/-!
### Declarations about propositional connectives

def Iff.eq := propext` instead of `lemma Iff.eq := propext`
@[nolint defLemma] alias Iff.eq := propext

lemma iff_eq_eq : (a ↔ b) = (a = b) := propext ⟨propext, Eq.to_iff⟩

-- They were not used in Lean 3 and there are already lemmas with those names in Lean 4
#noalign eq_false

def dec (p : Prop) : Decidable p := by infer_instance
#align classical.dec Classical.dec

def decPred (p : α → Prop) : DecidablePred p := by infer_instance
#align classical.dec_pred Classical.decPred

def decRel (p : α → α → Prop) : DecidableRel p := by infer_instance
#align classical.dec_rel Classical.decRel

def decEq (α : Sort u) : DecidableEq α := by infer_instance
#align classical.dec_eq Classical.decEq

def existsCases (H0 : C) (H : ∀ a, p a → C) : C :=
  if h : ∃ a, p a then H (Classical.choose h) (Classical.choose_spec h) else H0
#align classical.exists_cases Classical.existsCases

def subtype_of_exists {α : Type*} {P : α → Prop} (h : ∃ x, P x) : { x // P x } :=
  ⟨Classical.choose h, Classical.choose_spec h⟩
#align classical.subtype_of_exists Classical.subtype_of_exists

def byContradiction' {α : Sort*} (H : ¬(α → False)) : α :=
  Classical.choice <| (peirce _ False) fun h ↦ (H fun a ↦ h ⟨a⟩).elim
#align classical.by_contradiction' Classical.byContradiction'

def choice_of_byContradiction' {α : Sort*} (contra : ¬(α → False) → α) : Nonempty α → α :=
  fun H ↦ contra H.elim
#align classical.choice_of_by_contradiction' Classical.choice_of_byContradiction'

def Exists.classicalRecOn {p : α → Prop} (h : ∃ a, p a) {C} (H : ∀ a, p a → C) : C :=
  H (Classical.choose h) (Classical.choose_spec h)
#align exists.classical_rec_on Exists.classicalRecOn

def : (∃ (x : _) (_ : p x), q x) ↔ ∃ x, p x ∧ q x :=
  ⟨fun ⟨x, px, qx⟩ ↦ ⟨x, px, qx⟩, fun ⟨x, px, qx⟩ ↦ ⟨x, px, qx⟩⟩
#align bex_def bex_def