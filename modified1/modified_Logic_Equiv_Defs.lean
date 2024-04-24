def EquivLike.toEquiv {F} [EquivLike F α β] (f : F) : α ≃ β where
  toFun := f
  invFun := EquivLike.inv f
  left_inv := EquivLike.left_inv f
  right_inv := EquivLike.right_inv f

/-- Any type satisfying `EquivLike` can be cast into `Equiv` via `EquivLike.toEquiv`. -/
instance {F} [EquivLike F α β] : CoeTC F (α ≃ β) :=
  ⟨EquivLike.toEquiv⟩

/-- `Perm α` is the type of bijections from `α` to itself. -/
@[reducible]
def Equiv.Perm (α : Sort*) :=
  Equiv α α
#align equiv.perm Equiv.Perm

def refl (α : Sort*) : α ≃ α := ⟨id, id, fun _ => rfl, fun _ => rfl⟩
#align equiv.refl Equiv.refl

def symm (e : α ≃ β) : β ≃ α := ⟨e.invFun, e.toFun, e.right_inv, e.left_inv⟩
#align equiv.symm Equiv.symm

def Simps.symm_apply (e : α ≃ β) : β → α := e.symm
#align equiv.simps.symm_apply Equiv.Simps.symm_apply

def trans (e₁ : α ≃ β) (e₂ : β ≃ γ) : α ≃ γ :=
  ⟨e₂ ∘ e₁, e₁.symm ∘ e₂.symm, e₂.left_inv.comp e₁.left_inv, e₂.right_inv.comp e₁.right_inv⟩
#align equiv.trans Equiv.trans

def decidableEq (e : α ≃ β) [DecidableEq β] : DecidableEq α :=
  e.injective.decidableEq
#align equiv.decidable_eq Equiv.decidableEq

def inhabited [Inhabited β] (e : α ≃ β) : Inhabited α := ⟨e.symm default⟩
#align equiv.inhabited Equiv.inhabited

def unique [Unique β] (e : α ≃ β) : Unique α := e.symm.surjective.unique
#align equiv.unique Equiv.unique

def cast {α β : Sort _} (h : α = β) : α ≃ β :=
  ⟨cast h, cast h.symm, fun _ => by cases h; rfl, fun _ => by cases h; rfl⟩
#align equiv.cast Equiv.cast

def equivCongr (ab : α ≃ β) (cd : γ ≃ δ) : (α ≃ γ) ≃ (β ≃ δ) where
  toFun ac := (ab.symm.trans ac).trans cd
  invFun bd := ab.trans <| bd.trans <| cd.symm
  left_inv ac := by ext x; simp only [trans_apply, comp_apply, symm_apply_apply]
  right_inv ac := by ext x; simp only [trans_apply, comp_apply, apply_symm_apply]
#align equiv.equiv_congr Equiv.equivCongr

def permCongr : Perm α' ≃ Perm β' := equivCongr e e
#align equiv.perm_congr Equiv.permCongr

def (p : Equiv.Perm α') : e.permCongr p = (e.symm.trans p).trans e := rfl
#align equiv.perm_congr_def Equiv.permCongr_def

def equivOfIsEmpty (α β : Sort*) [IsEmpty α] [IsEmpty β] : α ≃ β :=
  ⟨isEmptyElim, isEmptyElim, isEmptyElim, isEmptyElim⟩
#align equiv.equiv_of_is_empty Equiv.equivOfIsEmpty

def equivEmpty (α : Sort u) [IsEmpty α] : α ≃ Empty := equivOfIsEmpty α _
#align equiv.equiv_empty Equiv.equivEmpty

def equivPEmpty (α : Sort v) [IsEmpty α] : α ≃ PEmpty.{u} := equivOfIsEmpty α _
#align equiv.equiv_pempty Equiv.equivPEmpty

def equivEmptyEquiv (α : Sort u) : α ≃ Empty ≃ IsEmpty α :=
  ⟨fun e => Function.isEmpty e, @equivEmpty α, fun e => ext fun x => (e x).elim, fun _ => rfl⟩
#align equiv.equiv_empty_equiv Equiv.equivEmptyEquiv

def propEquivPEmpty {p : Prop} (h : ¬p) : p ≃ PEmpty := @equivPEmpty p <| IsEmpty.prop_iff.2 h
#align equiv.prop_equiv_pempty Equiv.propEquivPEmpty

def equivOfUnique (α β : Sort _) [Unique.{u} α] [Unique.{v} β] : α ≃ β where
  toFun := default
  invFun := default
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
#align equiv.equiv_of_unique Equiv.equivOfUnique

def equivPUnit (α : Sort u) [Unique α] : α ≃ PUnit.{v} := equivOfUnique α _
#align equiv.equiv_punit Equiv.equivPUnit

def propEquivPUnit {p : Prop} (h : p) : p ≃ PUnit.{0} := @equivPUnit p <| uniqueProp h
#align equiv.prop_equiv_punit Equiv.propEquivPUnit

def ulift {α : Type v} : ULift.{u} α ≃ α :=
  ⟨ULift.down, ULift.up, ULift.up_down, ULift.down_up.{v, u}⟩
#align equiv.ulift Equiv.ulift

def plift : PLift α ≃ α := ⟨PLift.down, PLift.up, PLift.up_down, PLift.down_up⟩
#align equiv.plift Equiv.plift

def ofIff {P Q : Prop} (h : P ↔ Q) : P ≃ Q := ⟨h.mp, h.mpr, fun _ => rfl, fun _ => rfl⟩
#align equiv.of_iff Equiv.ofIff

def arrowCongr {α₁ β₁ α₂ β₂ : Sort*} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) : (α₁ → β₁) ≃ (α₂ → β₂) where
  toFun f := e₂ ∘ f ∘ e₁.symm
  invFun f := e₂.symm ∘ f ∘ e₁
  left_inv f := funext fun x => by simp only [comp_apply, symm_apply_apply]
  right_inv f := funext fun x => by simp only [comp_apply, apply_symm_apply]
#align equiv.arrow_congr_apply Equiv.arrowCongr_apply

def arrowCongr' {α₁ β₁ α₂ β₂ : Type*} (hα : α₁ ≃ α₂) (hβ : β₁ ≃ β₂) : (α₁ → β₁) ≃ (α₂ → β₂) :=
  Equiv.arrowCongr hα hβ
#align equiv.arrow_congr' Equiv.arrowCongr'

def conj (e : α ≃ β) : (α → α) ≃ (β → β) := arrowCongr e e
#align equiv.conj Equiv.conj

def punitEquivPUnit : PUnit.{v} ≃ PUnit.{w} :=
  ⟨fun _ => .unit, fun _ => .unit, fun ⟨⟩ => rfl, fun ⟨⟩ => rfl⟩
#align equiv.punit_equiv_punit Equiv.punitEquivPUnit

def propEquivBool : Prop ≃ Bool where
  toFun p := @decide p (Classical.propDecidable _)
  invFun b := b
  left_inv p := by simp [@Bool.decide_iff p (Classical.propDecidable _)]
  right_inv b := by cases b <;> simp
#align equiv.Prop_equiv_bool Equiv.propEquivBool

def arrowPUnitEquivPUnit (α : Sort*) : (α → PUnit.{v}) ≃ PUnit.{w} :=
  ⟨fun _ => .unit, fun _ _ => .unit, fun _ => rfl, fun _ => rfl⟩
#align equiv.arrow_punit_equiv_punit Equiv.arrowPUnitEquivPUnit

def piUnique [Unique α] (β : α → Sort*) : (∀ i, β i) ≃ β default where
  toFun f := f default
  invFun := uniqueElim
  left_inv f := by ext i; cases Unique.eq_default i; rfl
  right_inv x := rfl

/-- If `α` has a unique term, then the type of function `α → β` is equivalent to `β`. -/
@[simps! (config := .asFn) apply symm_apply]
def funUnique (α β) [Unique.{u} α] : (α → β) ≃ β := piUnique _
#align equiv.fun_unique Equiv.funUnique

def punitArrowEquiv (α : Sort*) : (PUnit.{u} → α) ≃ α := funUnique PUnit.{u} α
#align equiv.punit_arrow_equiv Equiv.punitArrowEquiv

def trueArrowEquiv (α : Sort*) : (True → α) ≃ α := funUnique _ _
#align equiv.true_arrow_equiv Equiv.trueArrowEquiv

def arrowPUnitOfIsEmpty (α β : Sort*) [IsEmpty α] : (α → β) ≃ PUnit.{u} where
  toFun _ := PUnit.unit
  invFun _ := isEmptyElim
  left_inv _ := funext isEmptyElim
  right_inv _ := rfl
#align equiv.arrow_punit_of_is_empty Equiv.arrowPUnitOfIsEmpty

def emptyArrowEquivPUnit (α : Sort*) : (Empty → α) ≃ PUnit.{u} := arrowPUnitOfIsEmpty _ _
#align equiv.empty_arrow_equiv_punit Equiv.emptyArrowEquivPUnit

def pemptyArrowEquivPUnit (α : Sort*) : (PEmpty → α) ≃ PUnit.{u} := arrowPUnitOfIsEmpty _ _
#align equiv.pempty_arrow_equiv_punit Equiv.pemptyArrowEquivPUnit

def falseArrowEquivPUnit (α : Sort*) : (False → α) ≃ PUnit.{u} := arrowPUnitOfIsEmpty _ _
#align equiv.false_arrow_equiv_punit Equiv.falseArrowEquivPUnit

def psigmaEquivSigma {α} (β : α → Type*) : (Σ' i, β i) ≃ Σ i, β i where
  toFun a := ⟨a.1, a.2⟩
  invFun a := ⟨a.1, a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
#align equiv.psigma_equiv_sigma Equiv.psigmaEquivSigma

def psigmaEquivSigmaPLift {α} (β : α → Sort*) : (Σ' i, β i) ≃ Σ i : PLift α, PLift (β i.down) where
  toFun a := ⟨PLift.up a.1, PLift.up a.2⟩
  invFun a := ⟨a.1.down, a.2.down⟩
  left_inv _ := rfl
  right_inv _ := rfl
#align equiv.psigma_equiv_sigma_plift Equiv.psigmaEquivSigmaPLift

def psigmaCongrRight {β₁ β₂ : α → Sort*} (F : ∀ a, β₁ a ≃ β₂ a) : (Σ' a, β₁ a) ≃ Σ' a, β₂ a where
  toFun a := ⟨a.1, F a.1 a.2⟩
  invFun a := ⟨a.1, (F a.1).symm a.2⟩
  left_inv | ⟨a, b⟩ => congr_arg (PSigma.mk a) <| symm_apply_apply (F a) b
  right_inv | ⟨a, b⟩ => congr_arg (PSigma.mk a) <| apply_symm_apply (F a) b
#align equiv.psigma_congr_right Equiv.psigmaCongrRight

def sigmaCongrRight {α} {β₁ β₂ : α → Type*} (F : ∀ a, β₁ a ≃ β₂ a) : (Σ a, β₁ a) ≃ Σ a, β₂ a where
  toFun a := ⟨a.1, F a.1 a.2⟩
  invFun a := ⟨a.1, (F a.1).symm a.2⟩
  left_inv | ⟨a, b⟩ => congr_arg (Sigma.mk a) <| symm_apply_apply (F a) b
  right_inv | ⟨a, b⟩ => congr_arg (Sigma.mk a) <| apply_symm_apply (F a) b
#align equiv.sigma_congr_right Equiv.sigmaCongrRight

def psigmaEquivSubtype {α : Type v} (P : α → Prop) : (Σ' i, P i) ≃ Subtype P where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
#align equiv.psigma_equiv_subtype Equiv.psigmaEquivSubtype

def sigmaPLiftEquivSubtype {α : Type v} (P : α → Prop) : (Σ i, PLift (P i)) ≃ Subtype P :=
  ((psigmaEquivSigma _).symm.trans
    (psigmaCongrRight fun _ => Equiv.plift)).trans (psigmaEquivSubtype P)
#align equiv.sigma_plift_equiv_subtype Equiv.sigmaPLiftEquivSubtype

def sigmaULiftPLiftEquivSubtype {α : Type v} (P : α → Prop) :
    (Σ i, ULift (PLift (P i))) ≃ Subtype P :=
  (sigmaCongrRight fun _ => Equiv.ulift).trans (sigmaPLiftEquivSubtype P)
#align equiv.sigma_ulift_plift_equiv_subtype Equiv.sigmaULiftPLiftEquivSubtype

def sigmaCongrRight {α} {β : α → Sort _} (F : ∀ a, Perm (β a)) : Perm (Σ a, β a) :=
  Equiv.sigmaCongrRight F
#align equiv.perm.sigma_congr_right Equiv.Perm.sigmaCongrRight

def sigmaCongrLeft {β : α₂ → Sort _} (e : α₁ ≃ α₂) :
    (Σ a : α₁, β (e a)) ≃ Σ a : α₂, β a where
  toFun a := ⟨e a.1, a.2⟩
  invFun a := ⟨e.symm a.1, (e.right_inv' a.1).symm ▸ a.2⟩
  -- Porting note: this was a pretty gnarly match already, and it got worse after porting
  left_inv := fun ⟨a, b⟩ =>
    match (motive := ∀ a' (h : a' = a), Sigma.mk _ (congr_arg e h.symm ▸ b) = ⟨a, b⟩)
      e.symm (e a), e.left_inv a with
    | _, rfl => rfl
  right_inv := fun ⟨a, b⟩ =>
    match (motive := ∀ a' (h : a' = a), Sigma.mk a' (h.symm ▸ b) = ⟨a, b⟩)
      e (e.symm a), e.apply_symm_apply _ with
    | _, rfl => rfl
#align equiv.sigma_congr_left_apply Equiv.sigmaCongrLeft_apply

def sigmaCongrLeft' {α₁ α₂} {β : α₁ → Sort _} (f : α₁ ≃ α₂) :
    (Σ a : α₁, β a) ≃ Σ a : α₂, β (f.symm a) := (sigmaCongrLeft f.symm).symm
#align equiv.sigma_congr_left' Equiv.sigmaCongrLeft'

def sigmaCongr {α₁ α₂} {β₁ : α₁ → Sort _} {β₂ : α₂ → Sort _} (f : α₁ ≃ α₂)
    (F : ∀ a, β₁ a ≃ β₂ (f a)) : Sigma β₁ ≃ Sigma β₂ :=
  (sigmaCongrRight F).trans (sigmaCongrLeft f)
#align equiv.sigma_congr Equiv.sigmaCongr

def sigmaEquivProd (α β : Type*) : (Σ _ : α, β) ≃ α × β :=
  ⟨fun a => ⟨a.1, a.2⟩, fun a => ⟨a.1, a.2⟩, fun ⟨_, _⟩ => rfl, fun ⟨_, _⟩ => rfl⟩
#align equiv.sigma_equiv_prod_apply Equiv.sigmaEquivProd_apply

def sigmaEquivProdOfEquiv {α β} {β₁ : α → Sort _} (F : ∀ a, β₁ a ≃ β) : Sigma β₁ ≃ α × β :=
  (sigmaCongrRight F).trans (sigmaEquivProd α β)
#align equiv.sigma_equiv_prod_of_equiv Equiv.sigmaEquivProdOfEquiv

def sigmaAssoc {α : Type*} {β : α → Type*} (γ : ∀ a : α, β a → Type*) :
    (Σ ab : Σ a : α, β a, γ ab.1 ab.2) ≃ Σ a : α, Σ b : β a, γ a b where
  toFun x := ⟨x.1.1, ⟨x.1.2, x.2⟩⟩
  invFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
#align equiv.sigma_assoc Equiv.sigmaAssoc

def ofBijective (f : α → β) (hf : Bijective f) : α ≃ β where
  toFun := f
  invFun := surjInv hf.surjective
  left_inv := leftInverse_surjInv hf
  right_inv := rightInverse_surjInv _
#align equiv.of_bijective Equiv.ofBijective

def congr {ra : α → α → Prop} {rb : β → β → Prop} (e : α ≃ β)
    (eq : ∀ a₁ a₂, ra a₁ a₂ ↔ rb (e a₁) (e a₂)) : Quot ra ≃ Quot rb where
  toFun := Quot.map e fun a₁ a₂ => (eq a₁ a₂).1
  invFun := Quot.map e.symm fun b₁ b₂ h =>
    (eq (e.symm b₁) (e.symm b₂)).2
      ((e.apply_symm_apply b₁).symm ▸ (e.apply_symm_apply b₂).symm ▸ h)
  left_inv := by rintro ⟨a⟩; simp only [Quot.map, Equiv.symm_apply_apply]
  right_inv := by rintro ⟨a⟩; simp only [Quot.map, Equiv.apply_symm_apply]
#align quot.congr Quot.congr

def congrRight {r r' : α → α → Prop} (eq : ∀ a₁ a₂, r a₁ a₂ ↔ r' a₁ a₂) :
    Quot r ≃ Quot r' := Quot.congr (Equiv.refl α) eq
#align quot.congr_right Quot.congrRight

def congrLeft {r : α → α → Prop} (e : α ≃ β) :
    Quot r ≃ Quot fun b b' => r (e.symm b) (e.symm b') :=
  Quot.congr e fun _ _ => by simp only [e.symm_apply_apply]
#align quot.congr_left Quot.congrLeft

def congr {ra : Setoid α} {rb : Setoid β} (e : α ≃ β)
    (eq : ∀ a₁ a₂, @Setoid.r α ra a₁ a₂ ↔ @Setoid.r β rb (e a₁) (e a₂)) :
    Quotient ra ≃ Quotient rb := Quot.congr e eq
#align quotient.congr Quotient.congr

def congrRight {r r' : Setoid α}
    (eq : ∀ a₁ a₂, @Setoid.r α r a₁ a₂ ↔ @Setoid.r α r' a₁ a₂) : Quotient r ≃ Quotient r' :=
  Quot.congrRight eq
#align quotient.congr_right Quotient.congrRight

structure Equiv (α : Sort*) (β : Sort _) where
  protected toFun : α → β
  protected invFun : β → α
  protected left_inv : LeftInverse invFun toFun
  protected right_inv : RightInverse invFun toFun
#align equiv Equiv