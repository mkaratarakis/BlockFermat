def posSumOfEncodable {ε : ℝ} (hε : 0 < ε) (ι) [Encodable ι] :
    { ε' : ι → ℝ // (∀ i, 0 < ε' i) ∧ ∃ c, HasSum ε' c ∧ c ≤ ε } := by
  let f n := ε / 2 / 2 ^ n
  have hf : HasSum f ε := hasSum_geometric_two' _
  have f0 : ∀ n, 0 < f n := fun n ↦ div_pos (half_pos hε) (pow_pos zero_lt_two _)
  refine' ⟨f ∘ Encodable.encode, fun i ↦ f0 _, _⟩
  rcases hf.summable.comp_injective (@Encodable.encode_injective ι _) with ⟨c, hg⟩
  refine' ⟨c, hg, hasSum_le_inj _ (@Encodable.encode_injective ι _) _ _ hg hf⟩
  · intro i _
    exact le_of_lt (f0 _)
  · intro n
    exact le_rfl
#align pos_sum_of_encodable posSumOfEncodable