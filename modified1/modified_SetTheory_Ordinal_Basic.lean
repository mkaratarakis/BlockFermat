def embeddingToCardinal : σ ↪ Cardinal.{u} :=
  Classical.choice nonempty_embedding_to_cardinal
#align embedding_to_cardinal embeddingToCardinal

def WellOrderingRel : σ → σ → Prop :=
  embeddingToCardinal ⁻¹'o (· < ·)
#align well_ordering_rel WellOrderingRel

def Ordinal : Type (u + 1) :=
  Quotient Ordinal.isEquivalent
#align ordinal Ordinal

def type (r : α → α → Prop) [wo : IsWellOrder α r] : Ordinal :=
  ⟦⟨α, r, wo⟩⟧
#align ordinal.type Ordinal.type

def typein (r : α → α → Prop) [IsWellOrder α r] (a : α) : Ordinal :=
  type (Subrel r { b | r b a })
#align ordinal.typein Ordinal.typein

def (r) [wo : IsWellOrder α r] : (⟦⟨α, r, wo⟩⟧ : Ordinal) = type r := by
  rfl
#align ordinal.type_def Ordinal.type_def

def initialSegOut {α β : Ordinal} (h : α ≤ β) :
    InitialSeg ((· < ·) : α.out.α → α.out.α → Prop) ((· < ·) : β.out.α → β.out.α → Prop) := by
  change α.out.r ≼i β.out.r
  rw [← Quotient.out_eq α, ← Quotient.out_eq β] at h; revert h
  cases Quotient.out α; cases Quotient.out β; exact Classical.choice
#align ordinal.initial_seg_out Ordinal.initialSegOut

def principalSegOut {α β : Ordinal} (h : α < β) :
    PrincipalSeg ((· < ·) : α.out.α → α.out.α → Prop) ((· < ·) : β.out.α → β.out.α → Prop) := by
  change α.out.r ≺i β.out.r
  rw [← Quotient.out_eq α, ← Quotient.out_eq β] at h; revert h
  cases Quotient.out α; cases Quotient.out β; exact Classical.choice
#align ordinal.principal_seg_out Ordinal.principalSegOut

def typein.principalSeg {α : Type u} (r : α → α → Prop) [IsWellOrder α r] :
    @PrincipalSeg α Ordinal.{u} r (· < ·) :=
  ⟨⟨⟨typein r, typein_injective r⟩, typein_lt_typein r⟩, type r,
    fun _ ↦ ⟨typein_surj r, fun ⟨a, h⟩ ↦ h ▸ typein_lt_type r a⟩⟩
#align ordinal.typein.principal_seg Ordinal.typein.principalSeg

def enum (r : α → α → Prop) [IsWellOrder α r] (o) (h : o < type r) : α :=
  (typein.principalSeg r).subrelIso ⟨o, h⟩

@[simp]
theorem typein_enum (r : α → α → Prop) [IsWellOrder α r] {o} (h : o < type r) :
    typein r (enum r o h) = o :=
  (typein.principalSeg r).apply_subrelIso _
#align ordinal.typein_enum Ordinal.typein_enum

def card : Ordinal → Cardinal :=
  Quotient.map WellOrder.α fun _ _ ⟨e⟩ => ⟨e.toEquiv⟩
#align ordinal.card Ordinal.card

def lift (o : Ordinal.{v}) : Ordinal.{max v u} :=
  Quotient.liftOn o (fun w => type <| ULift.down.{u} ⁻¹'o w.r) fun ⟨_, r, _⟩ ⟨_, s, _⟩ ⟨f⟩ =>
    Quot.sound
      ⟨(RelIso.preimage Equiv.ulift r).trans <| f.trans (RelIso.preimage Equiv.ulift s).symm⟩
#align ordinal.lift Ordinal.lift

def lift.initialSeg : @InitialSeg Ordinal.{u} Ordinal.{max u v} (· < ·) (· < ·) :=
  ⟨⟨⟨lift.{v}, fun _ _ => lift_inj.1⟩, lift_lt⟩, fun _ _ h => lift_down (le_of_lt h)⟩
#align ordinal.lift.initial_seg Ordinal.lift.initialSeg

def omega : Ordinal.{u} :=
  lift <| @type ℕ (· < ·) _
#align ordinal.omega Ordinal.omega

def enumIso (r : α → α → Prop) [IsWellOrder α r] : Subrel (· < ·) (· < type r) ≃r r :=
  { (typein.principalSeg r).subrelIso with
    toFun := fun x ↦ enum r x.1 x.2
    invFun := fun x ↦ ⟨typein r x, typein_lt_type r x⟩ }
#align ordinal.enum_iso Ordinal.enumIso

def enumIsoOut (o : Ordinal) : Set.Iio o ≃o o.out.α
    where
  toFun x :=
    enum (· < ·) x.1 <| by
      rw [type_lt]
      exact x.2
  invFun x := ⟨@typein _ (· < ·) (isWellOrder_out_lt _) x, typein_lt_self x⟩
  left_inv := fun ⟨o', h⟩ => Subtype.ext_val (typein_enum _ _)
  right_inv h := enum_typein _ _
  map_rel_iff' := by
    rintro ⟨a, _⟩ ⟨b, _⟩
    apply enum_le_enum'
#align ordinal.enum_iso_out Ordinal.enumIsoOut

def outOrderBotOfPos {o : Ordinal} (ho : 0 < o) : OrderBot o.out.α where
  bot_le := enum_zero_le' ho
#align ordinal.out_order_bot_of_pos Ordinal.outOrderBotOfPos

def univ : Ordinal.{max (u + 1) v} :=
  lift.{v, u + 1} (@type Ordinal (· < ·) _)
#align ordinal.univ Ordinal.univ

def lift.principalSeg : @PrincipalSeg Ordinal.{u} Ordinal.{max (u + 1) v} (· < ·) (· < ·) :=
  ⟨↑lift.initialSeg.{u, max (u + 1) v}, univ.{u, v}, by
    refine' fun b => inductionOn b _; intro β s _
    rw [univ, ← lift_umax]; constructor <;> intro h
    · rw [← lift_id (type s)] at h ⊢
      cases' lift_type_lt.{_,_,v}.1 h with f
      cases' f with f a hf
      exists a
      revert hf
      -- Porting note: apply inductionOn does not work, refine does
      refine inductionOn a ?_
      intro α r _ hf
      refine'
        lift_type_eq.{u, max (u + 1) v, max (u + 1) v}.2
          ⟨(RelIso.ofSurjective (RelEmbedding.ofMonotone _ _) _).symm⟩
      · exact fun b => enum r (f b) ((hf _).2 ⟨_, rfl⟩)
      · refine' fun a b h => (typein_lt_typein r).1 _
        rw [typein_enum, typein_enum]
        exact f.map_rel_iff.2 h
      · intro a'
        cases' (hf _).1 (typein_lt_type _ a') with b e
        exists b
        simp only [RelEmbedding.ofMonotone_coe]
        simp [e]
    · cases' h with a e
      rw [← e]
      refine inductionOn a ?_
      intro α r _
      exact lift_type_lt.{u, u + 1, max (u + 1) v}.2 ⟨typein.principalSeg r⟩⟩
#align ordinal.lift.principal_seg Ordinal.lift.principalSeg

def ord (c : Cardinal) : Ordinal :=
  let F := fun α : Type u => ⨅ r : { r // IsWellOrder α r }, @type α r.1 r.2
  Quot.liftOn c F
    (by
      suffices ∀ {α β}, α ≈ β → F α ≤ F β from
        fun α β h => (this h).antisymm (this (Setoid.symm h))
      rintro α β ⟨f⟩
      refine' le_ciInf_iff'.2 fun i => _
      haveI := @RelEmbedding.isWellOrder _ _ (f ⁻¹'o i.1) _ (↑(RelIso.preimage f i.1)) i.2
      exact
        (ciInf_le' _
              (Subtype.mk (f ⁻¹'o i.val)
                (@RelEmbedding.isWellOrder _ _ _ _ (↑(RelIso.preimage f i.1)) i.2))).trans_eq
          (Quot.sound ⟨RelIso.preimage f i.1⟩))
#align cardinal.ord Cardinal.ord

def is now Cardinal.mk'_def, not sure why
    simp only [mk'_def, e, card_type]
#align cardinal.card_ord Cardinal.card_ord

def gciOrdCard : GaloisCoinsertion ord card :=
  gc_ord_card.toGaloisCoinsertion fun c => c.card_ord.le
#align cardinal.gci_ord_card Cardinal.gciOrdCard

def ord.orderEmbedding : Cardinal ↪o Ordinal :=
  RelEmbedding.orderEmbeddingOfLTEmbedding
    (RelEmbedding.ofMonotone Cardinal.ord fun _ _ => Cardinal.ord_lt_ord.2)
#align cardinal.ord.order_embedding Cardinal.ord.orderEmbedding

def univ :=
  lift.{v, u + 1} #Ordinal

structure is registered on ordinals, where `⊥` is
`0`, the ordinal corresponding to the empty type, and `Inf` is the minimum for nonempty sets and `0`
for the empty set by convention.

## Notations

structure registering a well order on a type. Ordinals will be defined as a quotient
of this type. -/
structure WellOrder : Type (u + 1) where
  /-- The underlying type of the order. -/
  α : Type u
  /-- The underlying relation of the order. -/
  r : α → α → Prop
  /-- The proposition that `r` is a well-ordering for `α`. -/
  wo : IsWellOrder α r
set_option linter.uppercaseLean3 false in
#align Well_order WellOrder