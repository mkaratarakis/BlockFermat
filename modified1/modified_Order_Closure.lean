def conjBy {α β} [Preorder α] [Preorder β] (c : ClosureOperator α)
    (e : α ≃o β) : ClosureOperator β where
  toFun := e.conj c
  IsClosed b := c.IsClosed (e.symm b)
  monotone' _ _ h :=
    (map_le_map_iff e).mpr <| c.monotone <| (map_le_map_iff e.symm).mpr h
  le_closure' _ := e.symm_apply_le.mp (c.le_closure' _)
  idempotent' _ :=
    congrArg e <| Eq.trans (congrArg c (e.symm_apply_apply _)) (c.idempotent' _)
  isClosed_iff := Iff.trans c.isClosed_iff e.eq_symm_apply

lemma conjBy_refl {α} [Preorder α] (c : ClosureOperator α) :
    c.conjBy (OrderIso.refl α) = c := rfl

lemma conjBy_trans {α β γ} [Preorder α] [Preorder β] [Preorder γ]
    (e₁ : α ≃o β) (e₂ : β ≃o γ) (c : ClosureOperator α) :
    c.conjBy (e₁.trans e₂) = (c.conjBy e₁).conjBy e₂ := rfl

section PartialOrder

variable [PartialOrder α]

/-- The identity function as a closure operator. -/
@[simps!]
def id : ClosureOperator α where
  toOrderHom := OrderHom.id
  le_closure' _ := le_rfl
  idempotent' _ := rfl
  IsClosed _ := True
#align closure_operator.id ClosureOperator.id

def mk' (f : α → α) (hf₁ : Monotone f) (hf₂ : ∀ x, x ≤ f x) (hf₃ : ∀ x, f (f x) ≤ f x) :
    ClosureOperator α where
  toFun := f
  monotone' := hf₁
  le_closure' := hf₂
  idempotent' x := (hf₃ x).antisymm (hf₁ (hf₂ x))
#align closure_operator.mk' ClosureOperator.mk'

def mk₂ (f : α → α) (hf : ∀ x, x ≤ f x) (hmin : ∀ ⦃x y⦄, x ≤ f y → f x ≤ f y) : ClosureOperator α
    where
  toFun := f
  monotone' _ y hxy := hmin (hxy.trans (hf y))
  le_closure' := hf
  idempotent' _ := (hmin le_rfl).antisymm (hf _)
#align closure_operator.mk₂ ClosureOperator.mk₂

def ofPred (f : α → α) (p : α → Prop) (hf : ∀ x, x ≤ f x) (hfp : ∀ x, p (f x))
    (hmin : ∀ ⦃x y⦄, x ≤ y → p y → f x ≤ y) : ClosureOperator α where
  __ := mk₂ f hf fun _ y hxy => hmin hxy (hfp y)
  IsClosed := p
  isClosed_iff := ⟨fun hx ↦ (hmin le_rfl hx).antisymm <| hf _, fun hx ↦ hx ▸ hfp _⟩
#align closure_operator.mk₃ ClosureOperator.ofPred

def toCloseds (x : α) : c.Closeds := ⟨c x, c.isClosed_closure x⟩
#align closure_operator.to_closed ClosureOperator.toCloseds

def ofCompletePred (p : α → Prop) (hsinf : ∀ s, (∀ a ∈ s, p a) → p (sInf s)) : ClosureOperator α :=
  ofPred (fun a ↦ ⨅ b : {b // a ≤ b ∧ p b}, b) p
    (fun a ↦ by set_option tactic.skipAssignedInstances false in simp [forall_swap])
    (fun a ↦ hsinf _ <| forall_mem_range.2 fun b ↦ b.2.2)
    (fun a b hab hb ↦ iInf_le_of_le ⟨b, hab, hb⟩ le_rfl)

theorem sInf_isClosed {c : ClosureOperator α} {S : Set α}
    (H : ∀ x ∈ S, c.IsClosed x) : c.IsClosed (sInf S) :=
  isClosed_iff_closure_le.mpr <| le_of_le_of_eq c.monotone.map_sInf_le <|
    Eq.trans (biInf_congr (c.isClosed_iff.mp <| H · ·)) sInf_eq_iInf.symm

@[simp]
theorem closure_iSup_closure (f : ι → α) : c (⨆ i, c (f i)) = c (⨆ i, f i) :=
  le_antisymm (le_closure_iff.1 <| iSup_le fun i => c.monotone <| le_iSup f i) <|
    c.monotone <| iSup_mono fun _ => c.le_closure _
#align closure_operator.closure_supr_closure ClosureOperator.closure_iSup_closure

def OrderIso.equivClosureOperator {α β} [Preorder α] [Preorder β] (e : α ≃o β) :
    ClosureOperator α ≃ ClosureOperator β where
  toFun     c := c.conjBy e
  invFun    c := c.conjBy e.symm
  left_inv  c := Eq.trans (c.conjBy_trans _ _).symm
                 <| Eq.trans (congrArg _ e.self_trans_symm) c.conjBy_refl
  right_inv c := Eq.trans (c.conjBy_trans _ _).symm
                 <| Eq.trans (congrArg _ e.symm_trans_self) c.conjBy_refl

/-! ### Lower adjoint -/

def id [Preorder α] : LowerAdjoint (id : α → α) where
  toFun x := x
  gc' := GaloisConnection.id
#align lower_adjoint.id LowerAdjoint.id

def closureOperator : ClosureOperator α where
  toFun x := u (l x)
  monotone' := l.monotone
  le_closure' := l.le_closure
  idempotent' x := l.gc.u_l_u_eq_u (l x)
#align lower_adjoint.closure_operator LowerAdjoint.closureOperator

def closed : Set α := {x | u (l x) = x}
#align lower_adjoint.closed LowerAdjoint.closed

def toClosed (x : α) : l.closed :=
  ⟨u (l x), l.closure_is_closed x⟩
#align lower_adjoint.to_closed LowerAdjoint.toClosed

def GaloisConnection.lowerAdjoint [Preorder α] [Preorder β] {l : α → β} {u : β → α}
    (gc : GaloisConnection l u) : LowerAdjoint u
    where
  toFun := l
  gc' := gc
#align galois_connection.lower_adjoint GaloisConnection.lowerAdjoint

def GaloisConnection.closureOperator [PartialOrder α] [Preorder β] {l : α → β} {u : β → α}
    (gc : GaloisConnection l u) : ClosureOperator α :=
  gc.lowerAdjoint.closureOperator
#align galois_connection.closure_operator GaloisConnection.closureOperator

def ClosureOperator.gi [PartialOrder α] (c : ClosureOperator α) :
    GaloisInsertion c.toCloseds (↑) where
  choice x hx := ⟨x, isClosed_iff_closure_le.2 hx⟩
  gc _ y := y.2.closure_le_iff
  le_l_u _ := c.le_closure _
  choice_eq x hx := le_antisymm (c.le_closure x) hx
#align closure_operator.gi ClosureOperator.gi

structure ClosureOperator [Preorder α] extends α →o α where
  /-- An element is less than or equal its closure -/
  le_closure' : ∀ x, x ≤ toFun x
  /-- Closures are idempotent -/
  idempotent' : ∀ x, toFun (toFun x) = toFun x
  /-- Predicate for an element to be closed.

  By default, this is defined as `c.IsClosed x := (c x = x)` (see `isClosed_iff`).
  We allow an override to fix definitional equalities. -/
  IsClosed (x : α) : Prop := toFun x = x
  isClosed_iff {x : α} : IsClosed x ↔ toFun x = x := by aesop
#align closure_operator ClosureOperator

structure LowerAdjoint [Preorder α] [Preorder β] (u : β → α) where
  /-- The underlying function -/
  toFun : α → β
  /-- The underlying function is a lower adjoint. -/
  gc' : GaloisConnection toFun u
#align lower_adjoint LowerAdjoint