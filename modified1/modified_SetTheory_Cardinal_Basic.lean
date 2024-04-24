def α β : #α + #β = #(α ⊕ β)`.

def : #α * #β = #(α × β)`.

def α β : #α ≤ #β ↔ Nonempty (α ↪ β)`.

def α β : #α ^ #β = #(β → α)`.

def Cardinal : Type (u + 1) :=
  Quotient Cardinal.isEquivalent
#align cardinal Cardinal

def mk : Type u → Cardinal :=
  Quotient.mk'
#align cardinal.mk Cardinal.mk

def (α : Type u) : @Eq Cardinal ⟦α⟧ #α :=

def Cardinal.mk'_def

@[simp]
theorem mk_out (c : Cardinal) : #c.out = c :=

def outMkEquiv {α : Type v} : (#α).out ≃ α :=

def map (f : Type u → Type v) (hf : ∀ α β, α ≃ β → f α ≃ f β) : Cardinal.{u} → Cardinal.{v} :=
  Quotient.map f fun α β ⟨e⟩ => ⟨hf α β e⟩
#align cardinal.map Cardinal.map

def map₂ (f : Type u → Type v → Type w) (hf : ∀ α β γ δ, α ≃ β → γ ≃ δ → f α γ ≃ f β δ) :
    Cardinal.{u} → Cardinal.{v} → Cardinal.{w} :=
  Quotient.map₂ f fun α β ⟨e₁⟩ γ δ ⟨e₂⟩ => ⟨hf α β γ δ e₁ e₂⟩
#align cardinal.map₂ Cardinal.map₂

def lift (c : Cardinal.{v}) : Cardinal.{max v u} :=
  map ULift.{u, v} (fun _ _ e => Equiv.ulift.trans <| e.trans Equiv.ulift.symm) c
#align cardinal.lift Cardinal.lift

def (α β : Type u) : #α ≤ #β ↔ Nonempty (α ↪ β) :=

def Cardinal.le_def

theorem mk_le_of_injective {α β : Type u} {f : α → β} (hf : Injective f) : #α ≤ #β :=

def liftOrderEmbedding : Cardinal.{v} ↪o Cardinal.{max v u} :=
  OrderEmbedding.ofMapLEIff lift.{u, v} fun _ _ => lift_le
#align cardinal.lift_order_embedding Cardinal.liftOrderEmbedding

def (α β : Type u) : #α + #β = #(Sum α β) :=

def Cardinal.add_def

instance : NatCast Cardinal.{u} :=
  ⟨fun n => lift #(Fin n)⟩

def (α β : Type u) : #α * #β = #(α × β) :=

def Cardinal.mul_def

@[simp]
theorem mk_prod (α : Type u) (β : Type v) : #(α × β) = lift.{v, u} #α * lift.{u, v} #β :=

def (α β : Type u) : #α ^ #β = #(β → α) :=

def Cardinal.power_def

theorem mk_arrow (α : Type u) (β : Type v) : #(α → β) = (lift.{u} #β^lift.{v} #α) :=

def (c : Cardinal) : succ c = sInf { c' | c < c' } :=
  rfl
#align cardinal.succ_def Cardinal.succ_def

def IsLimit (c : Cardinal) : Prop :=
  c ≠ 0 ∧ IsSuccLimit c
#align cardinal.is_limit Cardinal.IsLimit

def sum {ι} (f : ι → Cardinal) : Cardinal :=
  mk (Σi, (f i).out)
#align cardinal.sum Cardinal.sum

def prod {ι : Type u} (f : ι → Cardinal) : Cardinal :=
  #(∀ i, (f i).out)

def aleph0 : Cardinal.{u} :=
  lift #ℕ

def powerlt (a b : Cardinal.{u}) : Cardinal.{u} :=
  ⨆ c : Iio b, a ^ (c : Cardinal)
#align cardinal.powerlt Cardinal.powerlt

def positivity_cardinal_pow : expr → tactic strictness
--   | q(@Pow.pow _ _ $(inst) $(a) $(b)) => do
--     let strictness_a ← core a
--     match strictness_a with
--       | positive p => positive <$> mk_app `` power_pos [b, p]
--       | _ => failed
--   |-- We already know that `0 ≤ x` for all `x : Cardinal`
--     _ =>
--     failed
-- #align tactic.positivity_cardinal_pow tactic.positivity_cardinal_pow