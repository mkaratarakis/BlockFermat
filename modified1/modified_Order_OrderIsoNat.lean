def natLT (f : ℕ → α) (H : ∀ n : ℕ, r (f n) (f (n + 1))) : ((· < ·) : ℕ → ℕ → Prop) ↪r r :=
  ofMonotone f <| Nat.rel_of_forall_rel_succ_of_lt r H
#align rel_embedding.nat_lt RelEmbedding.natLT

def natGT (f : ℕ → α) (H : ∀ n : ℕ, r (f (n + 1)) (f n)) : ((· > ·) : ℕ → ℕ → Prop) ↪r r :=
  haveI := IsStrictOrder.swap r
  RelEmbedding.swap (natLT f H)
#align rel_embedding.nat_gt RelEmbedding.natGT

def orderEmbeddingOfSet [DecidablePred (· ∈ s)] : ℕ ↪o ℕ :=
  (RelEmbedding.orderEmbeddingOfLTEmbedding
    (RelEmbedding.natLT (Nat.Subtype.ofNat s) fun _ => Nat.Subtype.lt_succ_self _)).trans
    (OrderEmbedding.subtype s)
#align nat.order_embedding_of_set Nat.orderEmbeddingOfSet

def Subtype.orderIsoOfNat : ℕ ≃o s := by
  classical
  exact
    RelIso.ofSurjective
      (RelEmbedding.orderEmbeddingOfLTEmbedding
        (RelEmbedding.natLT (Nat.Subtype.ofNat s) fun n => Nat.Subtype.lt_succ_self _))
      Nat.Subtype.ofNat_surjective
#align nat.subtype.order_iso_of_nat Nat.Subtype.orderIsoOfNat

def monotonicSequenceLimitIndex [Preorder α] (a : ℕ →o α) : ℕ :=
  sInf { n | ∀ m, n ≤ m → a n = a m }
#align monotonic_sequence_limit_index monotonicSequenceLimitIndex

def monotonicSequenceLimit [Preorder α] (a : ℕ →o α) :=
  a (monotonicSequenceLimitIndex a)
#align monotonic_sequence_limit monotonicSequenceLimit