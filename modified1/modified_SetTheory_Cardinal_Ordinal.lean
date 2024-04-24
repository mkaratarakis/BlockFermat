def alephIdx.initialSeg : @InitialSeg Cardinal Ordinal (· < ·) (· < ·) :=
  @RelEmbedding.collapse Cardinal Ordinal (· < ·) (· < ·) _ Cardinal.ord.orderEmbedding.ltEmbedding
#align cardinal.aleph_idx.initial_seg Cardinal.alephIdx.initialSeg

def alephIdx : Cardinal → Ordinal :=
  alephIdx.initialSeg
#align cardinal.aleph_idx Cardinal.alephIdx

def alephIdx.relIso : @RelIso Cardinal.{u} Ordinal.{u} (· < ·) (· < ·) :=
  @RelIso.ofSurjective Cardinal.{u} Ordinal.{u} (· < ·) (· < ·) alephIdx.initialSeg.{u} <|
    (InitialSeg.eq_or_principal alephIdx.initialSeg.{u}).resolve_right fun ⟨o, e⟩ => by
      have : ∀ c, alephIdx c < o := fun c => (e _).2 ⟨_, rfl⟩
      refine' Ordinal.inductionOn o _ this; intro α r _ h
      let s := ⨆ a, invFun alephIdx (Ordinal.typein r a)
      apply (lt_succ s).not_le
      have I : Injective.{u+2, u+2} alephIdx := alephIdx.initialSeg.toEmbedding.injective
      simpa only [typein_enum, leftInverse_invFun I (succ s)] using
        le_ciSup
          (Cardinal.bddAbove_range.{u, u} fun a : α => invFun alephIdx (Ordinal.typein r a))
          (Ordinal.enum r _ (h (succ s)))
#align cardinal.aleph_idx.rel_iso Cardinal.alephIdx.relIso

def Aleph'.relIso :=
  Cardinal.alephIdx.relIso.symm
#align cardinal.aleph'.rel_iso Cardinal.Aleph'.relIso

def aleph' : Ordinal → Cardinal :=
  Aleph'.relIso
#align cardinal.aleph' Cardinal.aleph'

def aleph'Equiv : Ordinal ≃ Cardinal :=
  ⟨aleph', alephIdx, alephIdx_aleph', aleph'_alephIdx⟩
#align cardinal.aleph'_equiv Cardinal.aleph'Equiv

def aleph (o : Ordinal) : Cardinal :=
  aleph' (ω + o)
#align cardinal.aleph Cardinal.aleph

def beth (o : Ordinal.{u}) : Cardinal.{u} :=
  limitRecOn o aleph0 (fun _ x => (2 : Cardinal) ^ x) fun a _ IH => ⨆ b : Iio a, IH b.1 b.2
#align cardinal.beth Cardinal.beth

def _ _).2 ⟨⟨fun a => [a], fun _ => by simp⟩⟩) <|
      calc
        #(List α) = sum fun n : ℕ => #α ^ (n : Cardinal.{u}) := mk_list_eq_sum_pow α