def id (r : α → α → Prop) : r →r r :=
  ⟨fun x => x, fun x => x⟩
#align rel_hom.id RelHom.id

def comp (g : s →r t) (f : r →r s) : r →r t :=
  ⟨fun x => g (f x), fun h => g.2 (f.2 h)⟩
#align rel_hom.comp RelHom.comp

def swap (f : r →r s) : swap r →r swap s :=
  ⟨f, f.map_rel⟩
#align rel_hom.swap RelHom.swap

def preimage (f : α → β) (s : β → β → Prop) : f ⁻¹'o s →r s :=
  ⟨f, id⟩
#align rel_hom.preimage RelHom.preimage

def Subtype.relEmbedding {X : Type*} (r : X → X → Prop) (p : X → Prop) :
    (Subtype.val : Subtype p → X) ⁻¹'o r ↪r r :=
  ⟨Embedding.subtype p, Iff.rfl⟩
#align subtype.rel_embedding Subtype.relEmbedding

def toRelHom (f : r ↪r s) : r →r s where
  toFun := f.toEmbedding.toFun
  map_rel' := (map_rel_iff' f).mpr
#align rel_embedding.to_rel_hom RelEmbedding.toRelHom

def refl (r : α → α → Prop) : r ↪r r :=
  ⟨Embedding.refl _, Iff.rfl⟩
#align rel_embedding.refl RelEmbedding.refl

def trans (f : r ↪r s) (g : s ↪r t) : r ↪r t :=
  ⟨f.1.trans g.1, by simp [f.map_rel_iff, g.map_rel_iff]⟩
#align rel_embedding.trans RelEmbedding.trans

def swap (f : r ↪r s) : swap r ↪r swap s :=
  ⟨f.toEmbedding, f.map_rel_iff⟩
#align rel_embedding.swap RelEmbedding.swap

def preimage (f : α ↪ β) (s : β → β → Prop) : f ⁻¹'o s ↪r s :=
  ⟨f, Iff.rfl⟩
#align rel_embedding.preimage RelEmbedding.preimage

def Quotient.mkRelHom [Setoid α] {r : α → α → Prop}
    (H : ∀ (a₁ b₁ a₂ b₂ : α), a₁ ≈ a₂ → b₁ ≈ b₂ → r a₁ b₁ = r a₂ b₂) : r →r Quotient.lift₂ r H :=
  ⟨@Quotient.mk' α _, id⟩
#align quotient.mk_rel_hom Quotient.mkRelHom

def Quotient.outRelEmbedding [Setoid α] {r : α → α → Prop}
    (H : ∀ (a₁ b₁ a₂ b₂ : α), a₁ ≈ a₂ → b₁ ≈ b₂ → r a₁ b₁ = r a₂ b₂) : Quotient.lift₂ r H ↪r r :=
  ⟨Embedding.quotientOut α, by
    refine' @fun x y => Quotient.inductionOn₂ x y fun a b => _
    apply iff_iff_eq.2 (H _ _ _ _ _ _) <;> apply Quotient.mk_out⟩
#align quotient.out_rel_embedding Quotient.outRelEmbedding

def Quotient.out'RelEmbedding {_ : Setoid α} {r : α → α → Prop}
    (H : ∀ (a₁ b₁ a₂ b₂ : α), a₁ ≈ a₂ → b₁ ≈ b₂ → r a₁ b₁ = r a₂ b₂) :
    (fun a b => Quotient.liftOn₂' a b r H) ↪r r :=
  { Quotient.outRelEmbedding H with toFun := Quotient.out' }
#align rel_embedding.quotient.out'_rel_embedding Quotient.out'RelEmbedding

def ofMapRelIff (f : α → β) [IsAntisymm α r] [IsRefl β s] (hf : ∀ a b, s (f a) (f b) ↔ r a b) :
    r ↪r s where
  toFun := f
  inj' _ _ h := antisymm ((hf _ _).1 (h ▸ refl _)) ((hf _ _).1 (h ▸ refl _))
  map_rel_iff' := hf _ _
#align rel_embedding.of_map_rel_iff RelEmbedding.ofMapRelIff

def ofMonotone [IsTrichotomous α r] [IsAsymm β s] (f : α → β) (H : ∀ a b, r a b → s (f a) (f b)) :
    r ↪r s := by
  haveI := @IsAsymm.isIrrefl β s _
  refine' ⟨⟨f, fun a b e => _⟩, @fun a b => ⟨fun h => _, H _ _⟩⟩
  · refine' ((@trichotomous _ r _ a b).resolve_left _).resolve_right _ <;>
      exact fun h => @irrefl _ s _ _ (by simpa [e] using H _ _ h)
  · refine' (@trichotomous _ r _ a b).resolve_right (Or.rec (fun e => _) fun h' => _)
    · subst e
      exact irrefl _ h
    · exact asymm (H _ _ h') h
#align rel_embedding.of_monotone RelEmbedding.ofMonotone

def ofIsEmpty (r : α → α → Prop) (s : β → β → Prop) [IsEmpty α] : r ↪r s :=
  ⟨Embedding.ofIsEmpty, @fun a => isEmptyElim a⟩
#align rel_embedding.of_is_empty RelEmbedding.ofIsEmpty

def sumLiftRelInl (r : α → α → Prop) (s : β → β → Prop) : r ↪r Sum.LiftRel r s where
  toFun := Sum.inl
  inj' := Sum.inl_injective
  map_rel_iff' := Sum.liftRel_inl_inl
#align rel_embedding.sum_lift_rel_inl RelEmbedding.sumLiftRelInl

def sumLiftRelInr (r : α → α → Prop) (s : β → β → Prop) : s ↪r Sum.LiftRel r s where
  toFun := Sum.inr
  inj' := Sum.inr_injective
  map_rel_iff' := Sum.liftRel_inr_inr
#align rel_embedding.sum_lift_rel_inr RelEmbedding.sumLiftRelInr

def sumLiftRelMap (f : r ↪r s) (g : t ↪r u) : Sum.LiftRel r t ↪r Sum.LiftRel s u where
  toFun := Sum.map f g
  inj' := f.injective.sum_map g.injective
  map_rel_iff' := by rintro (a | b) (c | d) <;> simp [f.map_rel_iff, g.map_rel_iff]
#align rel_embedding.sum_lift_rel_map RelEmbedding.sumLiftRelMap

def sumLexInl (r : α → α → Prop) (s : β → β → Prop) : r ↪r Sum.Lex r s where
  toFun := Sum.inl
  inj' := Sum.inl_injective
  map_rel_iff' := Sum.lex_inl_inl
#align rel_embedding.sum_lex_inl RelEmbedding.sumLexInl

def sumLexInr (r : α → α → Prop) (s : β → β → Prop) : s ↪r Sum.Lex r s where
  toFun := Sum.inr
  inj' := Sum.inr_injective
  map_rel_iff' := Sum.lex_inr_inr
#align rel_embedding.sum_lex_inr RelEmbedding.sumLexInr

def sumLexMap (f : r ↪r s) (g : t ↪r u) : Sum.Lex r t ↪r Sum.Lex s u where
  toFun := Sum.map f g
  inj' := f.injective.sum_map g.injective
  map_rel_iff' := by rintro (a | b) (c | d) <;> simp [f.map_rel_iff, g.map_rel_iff]
#align rel_embedding.sum_lex_map RelEmbedding.sumLexMap

def prodLexMkLeft (s : β → β → Prop) {a : α} (h : ¬r a a) : s ↪r Prod.Lex r s where
  toFun := Prod.mk a
  inj' := Prod.mk.inj_left a
  map_rel_iff' := by simp [Prod.lex_def, h]
#align rel_embedding.prod_lex_mk_left RelEmbedding.prodLexMkLeft

def prodLexMkRight (r : α → α → Prop) {b : β} (h : ¬s b b) : r ↪r Prod.Lex r s where
  toFun a := (a, b)
  inj' := Prod.mk.inj_right b
  map_rel_iff' := by simp [Prod.lex_def, h]
#align rel_embedding.prod_lex_mk_right RelEmbedding.prodLexMkRight

def prodLexMap (f : r ↪r s) (g : t ↪r u) : Prod.Lex r t ↪r Prod.Lex s u where
  toFun := Prod.map f g
  inj' := f.injective.Prod_map g.injective
  map_rel_iff' := by simp [Prod.lex_def, f.map_rel_iff, g.map_rel_iff, f.inj]
#align rel_embedding.prod_lex_map RelEmbedding.prodLexMap

def toRelEmbedding (f : r ≃r s) : r ↪r s :=
  ⟨f.toEquiv.toEmbedding, f.map_rel_iff'⟩
#align rel_iso.to_rel_embedding RelIso.toRelEmbedding

def symm (f : r ≃r s) : s ≃r r :=
  ⟨f.toEquiv.symm, @fun a b => by erw [← f.map_rel_iff, f.1.apply_symm_apply, f.1.apply_symm_apply]⟩
#align rel_iso.symm RelIso.symm

def Simps.apply (h : r ≃r s) : α → β :=
  h
#align rel_iso.simps.apply RelIso.Simps.apply

def Simps.symm_apply (h : r ≃r s) : β → α :=
  h.symm
#align rel_iso.simps.symm_apply RelIso.Simps.symm_apply

def refl (r : α → α → Prop) : r ≃r r :=
  ⟨Equiv.refl _, Iff.rfl⟩
#align rel_iso.refl RelIso.refl

def trans (f₁ : r ≃r s) (f₂ : s ≃r t) : r ≃r t :=
  ⟨f₁.toEquiv.trans f₂.toEquiv, f₂.map_rel_iff.trans f₁.map_rel_iff⟩
#align rel_iso.trans RelIso.trans

def (r : α → α → Prop) : default = RelIso.refl r :=
  rfl
#align rel_iso.default_def RelIso.default_def

def cast {α β : Type u} {r : α → α → Prop} {s : β → β → Prop} (h₁ : α = β)
    (h₂ : HEq r s) : r ≃r s :=
  ⟨Equiv.cast h₁, @fun a b => by
    subst h₁
    rw [eq_of_heq h₂]
    rfl⟩
#align rel_iso.cast RelIso.cast

def swap (f : r ≃r s) : swap r ≃r swap s :=
  ⟨f.toEquiv, f.map_rel_iff⟩
#align rel_iso.swap RelIso.swap

def preimage (f : α ≃ β) (s : β → β → Prop) : f ⁻¹'o s ≃r s :=
  ⟨f, Iff.rfl⟩
#align rel_iso.preimage RelIso.preimage

def ofSurjective (f : r ↪r s) (H : Surjective f) : r ≃r s :=
  ⟨Equiv.ofBijective f ⟨f.injective, H⟩, f.map_rel_iff⟩
#align rel_iso.of_surjective RelIso.ofSurjective

def sumLexCongr {α₁ α₂ β₁ β₂ r₁ r₂ s₁ s₂} (e₁ : @RelIso α₁ β₁ r₁ s₁) (e₂ : @RelIso α₂ β₂ r₂ s₂) :
    Sum.Lex r₁ r₂ ≃r Sum.Lex s₁ s₂ :=
  ⟨Equiv.sumCongr e₁.toEquiv e₂.toEquiv, @fun a b => by
    cases' e₁ with f hf; cases' e₂ with g hg; cases a <;> cases b <;> simp [hf, hg]⟩
#align rel_iso.sum_lex_congr RelIso.sumLexCongr

def prodLexCongr {α₁ α₂ β₁ β₂ r₁ r₂ s₁ s₂} (e₁ : @RelIso α₁ β₁ r₁ s₁) (e₂ : @RelIso α₂ β₂ r₂ s₂) :
    Prod.Lex r₁ r₂ ≃r Prod.Lex s₁ s₂ :=
  ⟨Equiv.prodCongr e₁.toEquiv e₂.toEquiv, by simp [Prod.lex_def, e₁.map_rel_iff, e₂.map_rel_iff,
    e₁.injective.eq_iff]⟩
#align rel_iso.prod_lex_congr RelIso.prodLexCongr

def relIsoOfIsEmpty (r : α → α → Prop) (s : β → β → Prop) [IsEmpty α] [IsEmpty β] : r ≃r s :=
  ⟨Equiv.equivOfIsEmpty α β, @fun a => isEmptyElim a⟩
#align rel_iso.rel_iso_of_is_empty RelIso.relIsoOfIsEmpty

def relIsoOfUniqueOfIrrefl (r : α → α → Prop) (s : β → β → Prop) [IsIrrefl α r]
    [IsIrrefl β s] [Unique α] [Unique β] : r ≃r s :=
  ⟨Equiv.equivOfUnique α β, iff_of_false (not_rel_of_subsingleton s _ _)
      (not_rel_of_subsingleton r _ _) ⟩
#align rel_iso.rel_iso_of_unique_of_irrefl RelIso.relIsoOfUniqueOfIrrefl

def relIsoOfUniqueOfRefl (r : α → α → Prop) (s : β → β → Prop) [IsRefl α r] [IsRefl β s]
    [Unique α] [Unique β] : r ≃r s :=
  ⟨Equiv.equivOfUnique α β, iff_of_true (rel_of_subsingleton s _ _) (rel_of_subsingleton r _ _)⟩
#align rel_iso.rel_iso_of_unique_of_refl RelIso.relIsoOfUniqueOfRefl

structure RelHom {α β : Type*} (r : α → α → Prop) (s : β → β → Prop) where
  /-- The underlying function of a `RelHom` -/
  toFun : α → β
  /-- A `RelHom` sends related elements to related elements -/
  map_rel' : ∀ {a b}, r a b → s (toFun a) (toFun b)
#align rel_hom RelHom

structure RelEmbedding {α β : Type*} (r : α → α → Prop) (s : β → β → Prop) extends α ↪ β where
  /-- Elements are related iff they are related after apply a `RelEmbedding` -/
  map_rel_iff' : ∀ {a b}, s (toEmbedding a) (toEmbedding b) ↔ r a b
#align rel_embedding RelEmbedding

structure RelIso {α β : Type*} (r : α → α → Prop) (s : β → β → Prop) extends α ≃ β where
  /-- Elements are related iff they are related after apply a `RelIso` -/
  map_rel_iff' : ∀ {a b}, s (toEquiv a) (toEquiv b) ↔ r a b
#align rel_iso RelIso