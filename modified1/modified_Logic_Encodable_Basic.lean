def decidableEqOfEncodable (α) [Encodable α] : DecidableEq α
  | _, _ => decidable_of_iff _ encode_inj
#align encodable.decidable_eq_of_encodable Encodable.decidableEqOfEncodable

def ofLeftInjection [Encodable α] (f : β → α) (finv : α → Option β)
    (linv : ∀ b, finv (f b) = some b) : Encodable β :=
  ⟨fun b => encode (f b), fun n => (decode n).bind finv, fun b => by
    simp [Encodable.encodek, linv]⟩
#align encodable.of_left_injection Encodable.ofLeftInjection

def ofLeftInverse [Encodable α] (f : β → α) (finv : α → β) (linv : ∀ b, finv (f b) = b) :
    Encodable β :=
  ofLeftInjection f (some ∘ finv) fun b => congr_arg some (linv b)
#align encodable.of_left_inverse Encodable.ofLeftInverse

def ofEquiv (α) [Encodable α] (e : β ≃ α) : Encodable β :=
  ofLeftInverse e e.symm e.left_inv
#align encodable.of_equiv Encodable.ofEquiv

def decode₂ (α) [Encodable α] (n : ℕ) : Option α :=
  (decode n).bind (Option.guard fun a => encode a = n)
#align encodable.decode₂ Encodable.decode₂

def decidableRangeEncode (α : Type*) [Encodable α] : DecidablePred (· ∈ Set.range (@encode α _)) :=
  fun x =>
  decidable_of_iff (Option.isSome (decode₂ α x))
    ⟨fun h => ⟨Option.get _ h, by rw [← decode₂_is_partial_inv (Option.get _ h), Option.some_get]⟩,
      fun ⟨n, hn⟩ => by rw [← hn, encodek₂]; exact rfl⟩
#align encodable.decidable_range_encode Encodable.decidableRangeEncode

def equivRangeEncode (α : Type*) [Encodable α] : α ≃ Set.range (@encode α _)
    where
  toFun := fun a : α => ⟨encode a, Set.mem_range_self _⟩
  invFun n :=
    Option.get _
      (show isSome (decode₂ α n.1) by cases' n.2 with x hx; rw [← hx, encodek₂]; exact rfl)
  left_inv a := by dsimp; rw [← Option.some_inj, Option.some_get, encodek₂]
  right_inv := fun ⟨n, x, hx⟩ => by
    apply Subtype.eq
    dsimp
    conv =>
      rhs
      rw [← hx]
    rw [encode_injective.eq_iff, ← Option.some_inj, Option.some_get, ← hx, encodek₂]
#align encodable.equiv_range_encode Encodable.equivRangeEncode

def _root_.Unique.encodable [Unique α] : Encodable α :=
  ⟨fun _ => 0, fun _ => some default, Unique.forall_iff.2 rfl⟩
#align unique.encodable Unique.encodable

def encodeSum : Sum α β → ℕ
  | Sum.inl a => 2 * encode a
  | Sum.inr b => 2 * encode b + 1
#align encodable.encode_sum Encodable.encodeSum

def decodeSum (n : ℕ) : Option (Sum α β) :=
  match boddDiv2 n with
  | (false, m) => (decode m : Option α).map Sum.inl
  | (_, m) => (decode m : Option β).map Sum.inr
#align encodable.decode_sum Encodable.decodeSum

def encodeSigma : Sigma γ → ℕ
  | ⟨a, b⟩ => pair (encode a) (encode b)
#align encodable.encode_sigma Encodable.encodeSigma

def decodeSigma (n : ℕ) : Option (Sigma γ) :=
  let (n₁, n₂) := unpair n
  (decode n₁).bind fun a => (decode n₂).map <| Sigma.mk a
#align encodable.decode_sigma Encodable.decodeSigma

def encodeSubtype : { a : α // P a } → ℕ
  | ⟨v,_⟩ => encode v
#align encodable.encode_subtype Encodable.encodeSubtype

def decodeSubtype (v : ℕ) : Option { a : α // P a } :=
  (decode v).bind fun a => if h : P a then some ⟨a, h⟩ else none
#align encodable.decode_subtype Encodable.decodeSubtype

def ofInj [Encodable β] (f : α → β) (hf : Injective f) : Encodable α :=
  ofLeftInjection f (partialInv f) fun _ => (partialInv_of_injective hf _ _).2 rfl
#align encodable.of_inj Encodable.ofInj

def ofCountable (α : Type*) [Countable α] : Encodable α :=
  Nonempty.some <|
    let ⟨f, hf⟩ := exists_injective_nat α
    ⟨ofInj f hf⟩
#align encodable.of_countable Encodable.ofCountable

def ULower (α : Type*) [Encodable α] : Type :=
  Set.range (Encodable.encode : α → ℕ)
#align ulower ULower

def equiv : α ≃ ULower α :=
  Encodable.equivRangeEncode α
#align ulower.equiv ULower.equiv

def down (a : α) : ULower α :=
  equiv α a
#align ulower.down ULower.down

def up (a : ULower α) : α :=
  (equiv α).symm a
#align ulower.up ULower.up

def good : Option α → Prop
  | some a => p a
  | none => False

private def decidable_good : DecidablePred (good p) :=
  fun n => by
    cases n <;> unfold good <;> dsimp <;> infer_instance
attribute [local instance] decidable_good

open Encodable

variable {p}

/-- Constructive choice function for a decidable subtype of an encodable type. -/
def chooseX (h : ∃ x, p x) : { a : α // p a } :=
  have : ∃ n, good p (decode n) :=
    let ⟨w, pw⟩ := h
    ⟨encode w, by simp [good, encodek, pw]⟩
  match (motive := ∀ o, good p o → { a // p a }) _, Nat.find_spec this with
  | some a, h => ⟨a, h⟩
#align encodable.choose_x Encodable.chooseX

def choose (h : ∃ x, p x) : α :=
  (chooseX h).1
#align encodable.choose Encodable.choose

def encode' (α) [Encodable α] : α ↪ ℕ :=
  ⟨Encodable.encode, Encodable.encode_injective⟩
#align encodable.encode' Encodable.encode'

def sequence {r : β → β → Prop} (f : α → β) (hf : Directed r f) : ℕ → α
  | 0 => default
  | n + 1 =>
    let p := Directed.sequence f hf n
    match (decode n: Option α) with
    | none => Classical.choose (hf p p)
    | some a => Classical.choose (hf p a)
#align directed.sequence Directed.sequence

def Quotient.rep (q : Quotient s) : α :=
  choose (exists_rep q)
#align quotient.rep Quotient.rep

def encodableQuotient : Encodable (Quotient s) :=
  ⟨fun q => encode q.rep, fun n => Quotient.mk'' <$> decode n, by
    rintro ⟨l⟩; dsimp; rw [encodek]; exact congr_arg some ⟦l⟧.rep_spec⟩
#align encodable_quotient encodableQuotient