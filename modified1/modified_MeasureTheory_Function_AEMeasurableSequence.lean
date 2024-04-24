def aeSeqSet (hf : ∀ i, AEMeasurable (f i) μ) (p : α → (ι → β) → Prop) : Set α :=
  (toMeasurable μ { x | (∀ i, f i x = (hf i).mk (f i) x) ∧ p x fun n => f n x }ᶜ)ᶜ
#align ae_seq_set aeSeqSet

def aeSeq (hf : ∀ i, AEMeasurable (f i) μ) (p : α → (ι → β) → Prop) : ι → α → β :=
  fun i x => ite (x ∈ aeSeqSet hf p) ((hf i).mk (f i) x) (⟨f i x⟩ : Nonempty β).some
#align ae_seq aeSeq