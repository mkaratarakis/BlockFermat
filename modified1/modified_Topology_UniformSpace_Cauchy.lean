def Cauchy (f : Filter α) :=
  NeBot f ∧ f ×ˢ f ≤ 𝓤 α
#align cauchy Cauchy

def IsComplete (s : Set α) :=
  ∀ f, Cauchy f → f ≤ 𝓟 s → ∃ x ∈ s, f ≤ 𝓝 x
#align is_complete IsComplete

def CauchySeq [Preorder β] (u : β → α) :=
  Cauchy (atTop.map u)
#align cauchy_seq CauchySeq

def TotallyBounded (s : Set α) : Prop :=
  ∀ d ∈ 𝓤 α, ∃ t : Set α, t.Finite ∧ s ⊆ ⋃ y ∈ t, { x | (x, y) ∈ d }
#align totally_bounded TotallyBounded

def setSeqAux (n : ℕ) : { s : Set α // s ∈ f ∧ s ×ˢ s ⊆ U n } :=
  -- Porting note: changed `∃ _ : s ∈ f, ..` to `s ∈ f ∧ ..`
  Classical.indefiniteDescription _ <| (cauchy_iff.1 hf).2 (U n) (U_mem n)
#align sequentially_complete.set_seq_aux SequentiallyComplete.setSeqAux

def setSeq (n : ℕ) : Set α :=
  ⋂ m ∈ Set.Iic n, (setSeqAux hf U_mem m).val
#align sequentially_complete.set_seq SequentiallyComplete.setSeq

def seq (n : ℕ) : α :=
  (hf.1.nonempty_of_mem (setSeq_mem hf U_mem n)).choose
#align sequentially_complete.seq SequentiallyComplete.seq