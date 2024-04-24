def Equiv.toEmbedding : α ↪ β :=
  ⟨f, f.injective⟩
#align equiv.to_embedding Equiv.toEmbedding

def refl (α : Sort*) : α ↪ α :=
  ⟨id, injective_id⟩
#align function.embedding.refl Function.Embedding.refl

def trans {α β γ} (f : α ↪ β) (g : β ↪ γ) : α ↪ γ :=
  ⟨g ∘ f, g.injective.comp f.injective⟩
#align function.embedding.trans Function.Embedding.trans

def congr {α : Sort u} {β : Sort v} {γ : Sort w} {δ : Sort x} (e₁ : α ≃ β) (e₂ : γ ≃ δ)
    (f : α ↪ γ) : β ↪ δ :=
  (Equiv.toEmbedding e₁.symm).trans (f.trans e₂.toEmbedding)
#align function.embedding.congr Function.Embedding.congr

def ofSurjective {α β} (f : β → α) (hf : Surjective f) : α ↪ β :=
  ⟨surjInv hf, injective_surjInv _⟩
#align function.embedding.of_surjective Function.Embedding.ofSurjective

def equivOfSurjective {α β} (f : α ↪ β) (hf : Surjective f) : α ≃ β :=
  Equiv.ofBijective f ⟨f.injective, hf⟩
#align function.embedding.equiv_of_surjective Function.Embedding.equivOfSurjective

def ofIsEmpty {α β} [IsEmpty α] : α ↪ β :=
  ⟨isEmptyElim, isEmptyElim⟩
#align function.embedding.of_is_empty Function.Embedding.ofIsEmpty

def setValue {α β} (f : α ↪ β) (a : α) (b : β) [∀ a', Decidable (a' = a)]
    [∀ a', Decidable (f a' = b)] : α ↪ β :=
  ⟨fun a' => if a' = a then b else if f a' = b then f a else f a', by
    intro x y (h : ite _ _ _ = ite _ _ _)
    -- TODO: once we have `cc` we can avoid all the manual cases below by doing
    -- split_ifs at h <;> (try subst b) <;> (try simp only [f.injective.eq_iff] at *) <;> cc
    split_ifs at h with h₁ h₂ _ _ h₅ h₆ <;>
        (try subst b) <;>
        (try simp only [f.injective.eq_iff, not_true_eq_false] at *)
    · rw [h₁,h₂]
    · rw [h₁,h]
    · rw [h₅, ← h]
    · exact h₆.symm
    · exfalso; exact h₅ h.symm
    · exfalso; exact h₁ h
    · exact h ⟩
#align function.embedding.set_value Function.Embedding.setValue

def some {α} : α ↪ Option α :=
  ⟨some, Option.some_injective α⟩
#align function.embedding.some Function.Embedding.some

def optionMap {α β} (f : α ↪ β) : Option α ↪ Option β :=
  ⟨Option.map f, Option.map_injective f.injective⟩
#align function.embedding.option_map Function.Embedding.optionMap

def subtype {α} (p : α → Prop) : Subtype p ↪ α :=
  ⟨Subtype.val, fun _ _ => Subtype.ext⟩
#align function.embedding.subtype Function.Embedding.subtype

def quotientOut (α) [s : Setoid α] : Quotient s ↪ α :=
  ⟨_, Quotient.out_injective⟩
#align function.embedding.quotient_out Function.Embedding.quotientOut

def punit {β : Sort*} (b : β) : PUnit ↪ β :=
  ⟨fun _ => b, by
    rintro ⟨⟩ ⟨⟩ _
    rfl⟩
#align function.embedding.punit Function.Embedding.punit

def sectl (α : Sort _) {β : Sort _} (b : β) : α ↪ α × β :=
  ⟨fun a => (a, b), fun _ _ h => congr_arg Prod.fst h⟩
#align function.embedding.sectl Function.Embedding.sectl

def sectr {α : Sort _} (a : α) (β : Sort _) : β ↪ α × β :=
  ⟨fun b => (a, b), fun _ _ h => congr_arg Prod.snd h⟩
#align function.embedding.sectr Function.Embedding.sectr

def prodMap {α β γ δ : Type*} (e₁ : α ↪ β) (e₂ : γ ↪ δ) : α × γ ↪ β × δ :=
  ⟨Prod.map e₁ e₂, e₁.injective.Prod_map e₂.injective⟩
#align function.embedding.prod_map Function.Embedding.prodMap

def pprodMap {α β γ δ : Sort*} (e₁ : α ↪ β) (e₂ : γ ↪ δ) : PProd α γ ↪ PProd β δ :=
  ⟨fun x => ⟨e₁ x.1, e₂ x.2⟩, e₁.injective.pprod_map e₂.injective⟩
#align function.embedding.pprod_map Function.Embedding.pprodMap

def sumMap {α β γ δ : Type*} (e₁ : α ↪ β) (e₂ : γ ↪ δ) : Sum α γ ↪ Sum β δ :=
  ⟨Sum.map e₁ e₂, e₁.injective.sum_map e₂.injective⟩
#align function.embedding.sum_map Function.Embedding.sumMap

def inl {α β : Type*} : α ↪ Sum α β :=
  ⟨Sum.inl, fun _ _ => Sum.inl.inj⟩
#align function.embedding.inl Function.Embedding.inl

def inr {α β : Type*} : β ↪ Sum α β :=
  ⟨Sum.inr, fun _ _ => Sum.inr.inj⟩
#align function.embedding.inr Function.Embedding.inr

def sigmaMk (a : α) : β a ↪ Σx, β x :=
  ⟨Sigma.mk a, sigma_mk_injective⟩
#align function.embedding.sigma_mk Function.Embedding.sigmaMk

def sigmaMap (f : α ↪ α') (g : ∀ a, β a ↪ β' (f a)) : (Σa, β a) ↪ Σa', β' a' :=
  ⟨Sigma.map f fun a => g a, f.injective.sigma_map fun a => (g a).injective⟩
#align function.embedding.sigma_map Function.Embedding.sigmaMap

def piCongrRight {α : Sort*} {β γ : α → Sort*} (e : ∀ a, β a ↪ γ a) : (∀ a, β a) ↪ ∀ a, γ a :=
  ⟨fun f a => e a (f a), fun _ _ h => funext fun a => (e a).injective (congr_fun h a)⟩
#align function.embedding.Pi_congr_right Function.Embedding.piCongrRight

def arrowCongrRight {α : Sort u} {β : Sort v} {γ : Sort w} (e : α ↪ β) : (γ → α) ↪ γ → β :=
  piCongrRight fun _ => e
#align function.embedding.arrow_congr_right Function.Embedding.arrowCongrRight

def arrowCongrLeft {α : Sort u} {β : Sort v} {γ : Sort w} [Inhabited γ] (e : α ↪ β) :
    (α → γ) ↪ β → γ :=
  ⟨fun f => extend e f default, fun f₁ f₂ h =>
    funext fun x => by simpa only [e.injective.extend_apply] using congr_fun h (e x)⟩
#align function.embedding.arrow_congr_left Function.Embedding.arrowCongrLeft

def subtypeMap {α β} {p : α → Prop} {q : β → Prop} (f : α ↪ β)
    (h : ∀ ⦃x⦄, p x → q (f x)) :
    { x : α // p x } ↪ { y : β // q y } :=
  ⟨Subtype.map f h, Subtype.map_injective h f.2⟩
#align function.embedding.subtype_map Function.Embedding.subtypeMap

def asEmbedding {p : β → Prop} (e : α ≃ Subtype p) : α ↪ β :=
  e.toEmbedding.trans (subtype p)
#align equiv.as_embedding Equiv.asEmbedding

def subtypeInjectiveEquivEmbedding (α β : Sort*) :
    { f : α → β // Injective f } ≃ (α ↪ β) where
  toFun f := ⟨f.val, f.property⟩
  invFun f := ⟨f, f.injective⟩
  left_inv _ := rfl
  right_inv _ := rfl
#align equiv.subtype_injective_equiv_embedding Equiv.subtypeInjectiveEquivEmbedding

def embeddingCongr {α β γ δ : Sort*} (h : α ≃ β) (h' : γ ≃ δ) : (α ↪ γ) ≃ (β ↪ δ) where
  toFun f := f.congr h h'
  invFun f := f.congr h.symm h'.symm
  left_inv x := by
    ext
    simp
  right_inv x := by
    ext
    simp
#align equiv.embedding_congr Equiv.embeddingCongr

def subtypeOrLeftEmbedding (p q : α → Prop) [DecidablePred p] :
    { x // p x ∨ q x } ↪ Sum { x // p x } { x // q x } :=
  ⟨fun x => if h : p x then Sum.inl ⟨x, h⟩ else Sum.inr ⟨x, x.prop.resolve_left h⟩, by
    intro x y
    dsimp only
    split_ifs <;> simp [Subtype.ext_iff]⟩
#align subtype_or_left_embedding subtypeOrLeftEmbedding

def Subtype.impEmbedding (p q : α → Prop) (h : ∀ x, p x → q x) : { x // p x } ↪ { x // q x } :=
  ⟨fun x => ⟨x, h x x.prop⟩, fun x y => by simp [Subtype.ext_iff]⟩
#align subtype.imp_embedding Subtype.impEmbedding

structure Embedding (α : Sort*) (β : Sort*) where
  /-- An embedding as a function. Use coercion instead. -/
  toFun : α → β
  /-- An embedding is an injective function. Use `Function.Embedding.injective` instead. -/
  inj' : Injective toFun
#align function.embedding Function.Embedding