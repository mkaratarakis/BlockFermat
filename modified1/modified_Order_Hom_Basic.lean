def OrderIsoClass.toOrderIso [LE α] [LE β] [EquivLike F α β] [OrderIsoClass F α β] (f : F) :
    α ≃o β :=
  { EquivLike.toEquiv f with map_rel_iff' := map_le_map_iff f }

/-- Any type satisfying `OrderIsoClass` can be cast into `OrderIso` via
`OrderIsoClass.toOrderIso`. -/
instance [LE α] [LE β] [EquivLike F α β] [OrderIsoClass F α β] : CoeTC F (α ≃o β) :=
  ⟨OrderIsoClass.toOrderIso⟩

-- See note [lower instance priority]
instance (priority := 100) OrderIsoClass.toOrderHomClass [LE α] [LE β]
    [EquivLike F α β] [OrderIsoClass F α β] : OrderHomClass F α β :=
  { EquivLike.toEmbeddingLike (E := F) with
    map_rel := fun f _ _ => (map_le_map_iff f).2 }
#align order_iso_class.to_order_hom_class OrderIsoClass.toOrderHomClass

def toOrderHom (f : F) : α →o β where
  toFun := f
  monotone' := OrderHomClass.monotone f

/-- Any type satisfying `OrderHomClass` can be cast into `OrderHom` via
`OrderHomClass.toOrderHom`. -/
instance : CoeTC F (α →o β) :=
  ⟨toOrderHom⟩

end OrderHomClass

section OrderIsoClass

section LE

variable [LE α] [LE β] [EquivLike F α β] [OrderIsoClass F α β]

-- Porting note: needed to add explicit arguments to map_le_map_iff
@[simp]
theorem map_inv_le_iff (f : F) {a : α} {b : β} : EquivLike.inv f b ≤ a ↔ b ≤ f a := by
  convert (map_le_map_iff f (a := EquivLike.inv f b) (b := a)).symm
  exact (EquivLike.right_inv f _).symm
#align map_inv_le_iff map_inv_le_iff

def Simps.coe (f : α →o β) : α → β := f

/- Porting note (#11215): TODO: all other DFunLike classes use `apply` instead of `coe`

def copy (f : α →o β) (f' : α → β) (h : f' = f) : α →o β :=
  ⟨f', h.symm.subst f.monotone'⟩
#align order_hom.copy OrderHom.copy

def id : α →o α :=
  ⟨_root_.id, monotone_id⟩
#align order_hom.id OrderHom.id

def {f g : α →o β} : f ≤ g ↔ ∀ x, f x ≤ g x :=
  Iff.rfl
#align order_hom.le_def OrderHom.le_def

def curry : (α × β →o γ) ≃o (α →o β →o γ) where
  toFun f := ⟨fun x ↦ ⟨Function.curry f x, fun _ _ h ↦ f.mono ⟨le_rfl, h⟩⟩, fun _ _ h _ =>
    f.mono ⟨h, le_rfl⟩⟩
  invFun f := ⟨Function.uncurry fun x ↦ f x, fun x y h ↦ (f.mono h.1 x.2).trans ((f y.1).mono h.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := by simp [le_def]
#align order_hom.curry OrderHom.curry

def comp (g : β →o γ) (f : α →o β) : α →o γ :=
  ⟨g ∘ f, g.mono.comp f.mono⟩
#align order_hom.comp OrderHom.comp

def compₘ : (β →o γ) →o (α →o β) →o α →o γ :=
  curry ⟨fun f : (β →o γ) × (α →o β) => f.1.comp f.2, fun _ _ h => comp_mono h.1 h.2⟩
#align order_hom.compₘ OrderHom.compₘ

def const (α : Type*) [Preorder α] {β : Type*} [Preorder β] : β →o α →o β where
  toFun b := ⟨Function.const α b, fun _ _ _ => le_rfl⟩
  monotone' _ _ h _ := h
#align order_hom.const OrderHom.const

def prod (f : α →o β) (g : α →o γ) : α →o β × γ :=
  ⟨fun x => (f x, g x), fun _ _ h => ⟨f.mono h, g.mono h⟩⟩
#align order_hom.prod OrderHom.prod

def prodₘ : (α →o β) →o (α →o γ) →o α →o β × γ :=
  curry ⟨fun f : (α →o β) × (α →o γ) => f.1.prod f.2, fun _ _ h => prod_mono h.1 h.2⟩
#align order_hom.prodₘ OrderHom.prodₘ

def diag : α →o α × α :=
  id.prod id
#align order_hom.diag OrderHom.diag

def onDiag (f : α →o α →o β) : α →o β :=
  (curry.symm f).comp diag
#align order_hom.on_diag OrderHom.onDiag

def fst : α × β →o α :=
  ⟨Prod.fst, fun _ _ h => h.1⟩
#align order_hom.fst OrderHom.fst

def snd : α × β →o β :=
  ⟨Prod.snd, fun _ _ h => h.2⟩
#align order_hom.snd OrderHom.snd

def prodIso : (α →o β × γ) ≃o (α →o β) × (α →o γ) where
  toFun f := (fst.comp f, snd.comp f)
  invFun f := f.1.prod f.2
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := forall_and.symm
#align order_hom.prod_iso OrderHom.prodIso

def prodMap (f : α →o β) (g : γ →o δ) : α × γ →o β × δ :=
  ⟨Prod.map f g, fun _ _ h => ⟨f.mono h.1, g.mono h.2⟩⟩
#align order_hom.prod_map OrderHom.prodMap

def _root_.Pi.evalOrderHom (i : ι) : (∀ j, π j) →o π i :=
  ⟨Function.eval i, Function.monotone_eval i⟩
#align pi.eval_order_hom Pi.evalOrderHom

def coeFnHom : (α →o β) →o α → β where
  toFun f := f
  monotone' _ _ h := h
#align order_hom.coe_fn_hom OrderHom.coeFnHom

def apply (x : α) : (α →o β) →o β :=
  (Pi.evalOrderHom x).comp coeFnHom
#align order_hom.apply OrderHom.apply

def pi (f : ∀ i, α →o π i) : α →o ∀ i, π i :=
  ⟨fun x i => f i x, fun _ _ h i => (f i).mono h⟩
#align order_hom.pi OrderHom.pi

def piIso : (α →o ∀ i, π i) ≃o ∀ i, α →o π i where
  toFun f i := (Pi.evalOrderHom i).comp f
  invFun := pi
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := forall_swap
#align order_hom.pi_iso OrderHom.piIso

def Subtype.val (p : α → Prop) : Subtype p →o α :=
  ⟨_root_.Subtype.val, fun _ _ h => h⟩
#align order_hom.subtype.val OrderHom.Subtype.val

def _root_.Subtype.orderEmbedding {p q : α → Prop} (h : ∀ a, p a → q a) :
    {x // p x} ↪o {x // q x} :=
  { Subtype.impEmbedding _ _ h with
    map_rel_iff' := by aesop }

/-- There is a unique monotone map from a subsingleton to itself. -/
instance unique [Subsingleton α] : Unique (α →o α) where
  default := OrderHom.id
  uniq _ := ext _ _ (Subsingleton.elim _ _)
#align order_hom.unique OrderHom.unique

def dual : (α →o β) ≃ (αᵒᵈ →o βᵒᵈ) where
  toFun f := ⟨(OrderDual.toDual : β → βᵒᵈ) ∘ (f : α → β) ∘
    (OrderDual.ofDual : αᵒᵈ → α), f.mono.dual⟩
  invFun f := ⟨OrderDual.ofDual ∘ f ∘ OrderDual.toDual, f.mono.dual⟩
  left_inv _ := rfl
  right_inv _ := rfl
#align order_hom.dual OrderHom.dual

def dualIso (α β : Type*) [Preorder α] [Preorder β] : (α →o β) ≃o (αᵒᵈ →o βᵒᵈ)ᵒᵈ where
  toEquiv := OrderHom.dual.trans OrderDual.toDual
  map_rel_iff' := Iff.rfl
#align order_hom.dual_iso OrderHom.dualIso

def withBotMap (f : α →o β) : WithBot α →o WithBot β :=
  ⟨WithBot.map f, f.mono.withBot_map⟩
#align order_hom.with_bot_map OrderHom.withBotMap

def withTopMap (f : α →o β) : WithTop α →o WithTop β :=
  ⟨WithTop.map f, f.mono.withTop_map⟩
#align order_hom.with_top_map OrderHom.withTopMap

def RelEmbedding.orderEmbeddingOfLTEmbedding [PartialOrder α] [PartialOrder β]
    (f : ((· < ·) : α → α → Prop) ↪r ((· < ·) : β → β → Prop)) : α ↪o β :=
  { f with
    map_rel_iff' := by
      intros
      simp [le_iff_lt_or_eq, f.map_rel_iff, f.injective.eq_iff] }
#align rel_embedding.order_embedding_of_lt_embedding RelEmbedding.orderEmbeddingOfLTEmbedding

def ltEmbedding : ((· < ·) : α → α → Prop) ↪r ((· < ·) : β → β → Prop) :=
  { f with map_rel_iff' := by intros; simp [lt_iff_le_not_le, f.map_rel_iff] }
#align order_embedding.lt_embedding OrderEmbedding.ltEmbedding

def dual : αᵒᵈ ↪o βᵒᵈ :=
  ⟨f.toEmbedding, f.map_rel_iff⟩
#align order_embedding.dual OrderEmbedding.dual

def withBotMap (f : α ↪o β) : WithBot α ↪o WithBot β :=
  { f.toEmbedding.optionMap with
    toFun := WithBot.map f,
    map_rel_iff' := @fun a b => WithBot.map_le_iff f f.map_rel_iff a b }
#align order_embedding.with_bot_map OrderEmbedding.withBotMap

def withTopMap (f : α ↪o β) : WithTop α ↪o WithTop β :=
  { f.dual.withBotMap.dual with toFun := WithTop.map f }
#align order_embedding.with_top_map OrderEmbedding.withTopMap

def ofMapLEIff {α β} [PartialOrder α] [Preorder β] (f : α → β) (hf : ∀ a b, f a ≤ f b ↔ a ≤ b) :
    α ↪o β :=
  RelEmbedding.ofMapRelIff f hf
#align order_embedding.of_map_le_iff OrderEmbedding.ofMapLEIff

def ofStrictMono {α β} [LinearOrder α] [Preorder β] (f : α → β) (h : StrictMono f) : α ↪o β :=
  ofMapLEIff f fun _ _ => h.le_iff_le
#align order_embedding.of_strict_mono OrderEmbedding.ofStrictMono

def subtype (p : α → Prop) : Subtype p ↪o α :=
  ⟨Function.Embedding.subtype p, Iff.rfl⟩
#align order_embedding.subtype OrderEmbedding.subtype

def toOrderHom {X Y : Type*} [Preorder X] [Preorder Y] (f : X ↪o Y) : X →o Y where
  toFun := f
  monotone' := f.monotone
#align order_embedding.to_order_hom OrderEmbedding.toOrderHom

def ofIsEmpty [IsEmpty α] : α ↪o β where
  toFun := isEmptyElim
  inj' := isEmptyElim
  map_rel_iff' {a} := isEmptyElim a

@[simp, norm_cast]
lemma coe_ofIsEmpty [IsEmpty α] : (ofIsEmpty : α ↪o β) = (isEmptyElim : α → β) := rfl

end OrderEmbedding

section RelHom

variable [PartialOrder α] [Preorder β]

namespace RelHom

variable (f : ((· < ·) : α → α → Prop) →r ((· < ·) : β → β → Prop))

/-- A bundled expression of the fact that a map between partial orders that is strictly monotone
is weakly monotone. -/
@[simps (config := .asFn)]
def toOrderHom : α →o β where
  toFun := f
  monotone' := StrictMono.monotone fun _ _ => f.map_rel
#align rel_hom.to_order_hom RelHom.toOrderHom

def toOrderEmbedding (e : α ≃o β) : α ↪o β :=
  e.toRelEmbedding
#align order_iso.to_order_embedding OrderIso.toOrderEmbedding

def refl (α : Type*) [LE α] : α ≃o α :=
  RelIso.refl (· ≤ ·)
#align order_iso.refl OrderIso.refl

def symm (e : α ≃o β) : β ≃o α := RelIso.symm e
#align order_iso.symm OrderIso.symm

def trans (e : α ≃o β) (e' : β ≃o γ) : α ≃o γ :=
  RelIso.trans e e'
#align order_iso.trans OrderIso.trans

def arrowCongr {α β γ δ} [Preorder α] [Preorder β] [Preorder γ] [Preorder δ]
    (f : α ≃o γ) (g : β ≃o δ) : (α →o β) ≃o (γ →o δ) where
  toFun  p := .comp g <| .comp p f.symm
  invFun p := .comp g.symm <| .comp p f
  left_inv p := DFunLike.coe_injective <| by
    change (g.symm ∘ g) ∘ p ∘ (f.symm ∘ f) = p
    simp only [← DFunLike.coe_eq_coe_fn, ← OrderIso.coe_trans, Function.id_comp,
               OrderIso.self_trans_symm, OrderIso.coe_refl, Function.comp_id]
  right_inv p := DFunLike.coe_injective <| by
    change (g ∘ g.symm) ∘ p ∘ (f ∘ f.symm) = p
    simp only [← DFunLike.coe_eq_coe_fn, ← OrderIso.coe_trans, Function.id_comp,
               OrderIso.symm_trans_self, OrderIso.coe_refl, Function.comp_id]
  map_rel_iff' {p q} := by
    simp only [Equiv.coe_fn_mk, OrderHom.le_def, OrderHom.comp_coe,
               OrderHomClass.coe_coe, Function.comp_apply, map_le_map_iff]
    exact Iff.symm f.forall_congr_left'

/-- If `α` and `β` are order-isomorphic then the two orders of order-homomorphisms
from `α` and `β` to themselves are order-isomorphic. -/
@[simps! apply symm_apply]
def conj {α β} [Preorder α] [Preorder β] (f : α ≃o β) : (α →o α) ≃ (β →o β) :=
  arrowCongr f f

/-- `Prod.swap` as an `OrderIso`. -/
def prodComm : α × β ≃o β × α where
  toEquiv := Equiv.prodComm α β
  map_rel_iff' := Prod.swap_le_swap
#align order_iso.prod_comm OrderIso.prodComm

def dualDual : α ≃o αᵒᵈᵒᵈ :=
  refl α
#align order_iso.dual_dual OrderIso.dualDual

def toRelIsoLT (e : α ≃o β) : ((· < ·) : α → α → Prop) ≃r ((· < ·) : β → β → Prop) :=
  ⟨e.toEquiv, lt_iff_lt e⟩
#align order_iso.to_rel_iso_lt OrderIso.toRelIsoLT

def ofRelIsoLT {α β} [PartialOrder α] [PartialOrder β]
    (e : ((· < ·) : α → α → Prop) ≃r ((· < ·) : β → β → Prop)) : α ≃o β :=
  ⟨e.toEquiv, by simp [le_iff_eq_or_lt, e.map_rel_iff, e.injective.eq_iff]⟩
#align order_iso.of_rel_iso_lt OrderIso.ofRelIsoLT

def ofCmpEqCmp {α β} [LinearOrder α] [LinearOrder β] (f : α → β) (g : β → α)
    (h : ∀ (a : α) (b : β), cmp a (g b) = cmp (f a) b) : α ≃o β :=
  have gf : ∀ a : α, a = g (f a) := by
    intro
    rw [← cmp_eq_eq_iff, h, cmp_self_eq_eq]
  { toFun := f, invFun := g, left_inv := fun a => (gf a).symm,
    right_inv := by
      intro
      rw [← cmp_eq_eq_iff, ← h, cmp_self_eq_eq],
    map_rel_iff' := by
      intros a b
      apply le_iff_le_of_cmp_eq_cmp
      convert (h a (f b)).symm
      apply gf }
#align order_iso.of_cmp_eq_cmp OrderIso.ofCmpEqCmp

def ofHomInv {F G : Type*} [FunLike F α β] [OrderHomClass F α β] [FunLike G β α]
    [OrderHomClass G β α] (f : F) (g : G)
    (h₁ : (f : α →o β).comp (g : β →o α) = OrderHom.id)
    (h₂ : (g : β →o α).comp (f : α →o β) = OrderHom.id) :
    α ≃o β where
  toFun := f
  invFun := g
  left_inv := DFunLike.congr_fun h₂
  right_inv := DFunLike.congr_fun h₁
  map_rel_iff' := @fun a b =>
    ⟨fun h => by
      replace h := map_rel g h
      rwa [Equiv.coe_fn_mk, show g (f a) = (g : β →o α).comp (f : α →o β) a from rfl,
        show g (f b) = (g : β →o α).comp (f : α →o β) b from rfl, h₂] at h,
      fun h => (f : α →o β).monotone h⟩
#align order_iso.of_hom_inv OrderIso.ofHomInv

def funUnique (α β : Type*) [Unique α] [Preorder β] : (α → β) ≃o β where
  toEquiv := Equiv.funUnique α β
  map_rel_iff' := by simp [Pi.le_def, Unique.forall_iff]
#align order_iso.fun_unique OrderIso.funUnique

def toOrderIso (e : α ≃ β) (h₁ : Monotone e) (h₂ : Monotone e.symm) : α ≃o β :=
  ⟨e, ⟨fun h => by simpa only [e.symm_apply_apply] using h₂ h, fun h => h₁ h⟩⟩
#align equiv.to_order_iso Equiv.toOrderIso

def orderIsoOfRightInverse (g : β → α) (hg : Function.RightInverse g f) : α ≃o β :=
  { OrderEmbedding.ofStrictMono f h_mono with
    toFun := f,
    invFun := g,
    left_inv := fun _ => h_mono.injective <| hg _,
    right_inv := hg }
#align strict_mono.order_iso_of_right_inverse StrictMono.orderIsoOfRightInverse

def OrderIso.dual [LE α] [LE β] (f : α ≃o β) : αᵒᵈ ≃o βᵒᵈ :=
  ⟨f.toEquiv, f.map_rel_iff⟩
#align order_iso.dual OrderIso.dual

def toDualTopEquiv [LE α] : WithBot αᵒᵈ ≃o (WithTop α)ᵒᵈ :=
  OrderIso.refl _
#align with_bot.to_dual_top_equiv WithBot.toDualTopEquiv

def toDualBotEquiv [LE α] : WithTop αᵒᵈ ≃o (WithBot α)ᵒᵈ :=
  OrderIso.refl _
#align with_top.to_dual_bot_equiv WithTop.toDualBotEquiv

def withTopCongr (e : α ≃o β) : WithTop α ≃o WithTop β :=
  { e.toOrderEmbedding.withTopMap with
    toEquiv := e.toEquiv.optionCongr }
#align order_iso.with_top_congr OrderIso.withTopCongr

def withBotCongr (e : α ≃o β) : WithBot α ≃o WithBot β :=
  { e.toOrderEmbedding.withBotMap with toEquiv := e.toEquiv.optionCongr }
#align order_iso.with_bot_congr OrderIso.withBotCongr

structure OrderHom (α β : Type*) [Preorder α] [Preorder β] where
  /-- The underlying function of an `OrderHom`. -/
  toFun : α → β
  /-- The underlying function of an `OrderHom` is monotone. -/
  monotone' : Monotone toFun
#align order_hom OrderHom

structure of `α →o β` is pointwise inequality: `f ≤ g ↔ ∀ a, f a ≤ g a`. -/
instance : Preorder (α →o β) :=
  @Preorder.lift (α →o β) (α → β) _ toFun

instance {β : Type*} [PartialOrder β] : PartialOrder (α →o β) :=
  @PartialOrder.lift (α →o β) (α → β) _ toFun ext

theorem le_def {f g : α →o β} : f ≤ g ↔ ∀ x, f x ≤ g x :=
  Iff.rfl
#align order_hom.le_def OrderHom.le_def