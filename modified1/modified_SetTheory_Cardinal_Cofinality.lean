def cof (r : α → α → Prop) : Cardinal :=
  sInf { c | ∃ S : Set α, (∀ a, ∃ b ∈ S, r a b) ∧ #S = c }

def StrictOrder.cof (r : α → α → Prop) : Cardinal :=
  Order.cof (swap rᶜ)
#align strict_order.cof StrictOrder.cof

def cof (o : Ordinal.{u}) : Cardinal.{u} :=
  o.liftOn (fun a => StrictOrder.cof a.r)
    (by
      rintro ⟨α, r, wo₁⟩ ⟨β, s, wo₂⟩ ⟨⟨f, hf⟩⟩
      haveI := wo₁; haveI := wo₂
      dsimp only
      apply @RelIso.cof_eq _ _ _ _ ?_ ?_
      · constructor
        exact @fun a b => not_iff_not.2 hf
      · dsimp only [swap]
        exact ⟨fun _ => irrefl _⟩
      · dsimp only [swap]
        exact ⟨fun _ => irrefl _⟩)
#align ordinal.cof Ordinal.cof

def IsFundamentalSequence (a o : Ordinal.{u}) (f : ∀ b < o, Ordinal.{u}) : Prop :=
  o ≤ a.cof.ord ∧ (∀ {i j} (hi hj), i < j → f i hi < f j hj) ∧ blsub.{u, u} o f = a
#align ordinal.is_fundamental_sequence Ordinal.IsFundamentalSequence

def IsStrongLimit (c : Cardinal) : Prop :=
  c ≠ 0 ∧ ∀ x < c, (2^x) < c
#align cardinal.is_strong_limit Cardinal.IsStrongLimit

def IsRegular (c : Cardinal) : Prop :=
  ℵ₀ ≤ c ∧ c ≤ c.ord.cof
#align cardinal.is_regular Cardinal.IsRegular

def IsInaccessible (c : Cardinal) :=
  ℵ₀ < c ∧ IsRegular c ∧ IsStrongLimit c
#align cardinal.is_inaccessible Cardinal.IsInaccessible