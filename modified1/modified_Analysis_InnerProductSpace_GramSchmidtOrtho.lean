def gramSchmidt [IsWellOrder ι (· < ·)] (f : ι → E) (n : ι) : E :=
  f n - ∑ i : Iio n, orthogonalProjection (𝕜 ∙ gramSchmidt f i) (f n)
termination_by n
decreasing_by exact mem_Iio.1 i.2
#align gram_schmidt gramSchmidt

def (f : ι → E) (n : ι) :
    gramSchmidt 𝕜 f n = f n - ∑ i in Iio n, orthogonalProjection (𝕜 ∙ gramSchmidt 𝕜 f i) (f n) := by
  rw [← sum_attach, attach_eq_univ, gramSchmidt]
#align gram_schmidt_def gramSchmidt_def

def 𝕜 f b, inner_sub_right, inner_sum, orthogonalProjection_singleton,
    inner_smul_right]
  rw [Finset.sum_eq_single_of_mem a (Finset.mem_Iio.mpr h₀)]
  · by_cases h : gramSchmidt 𝕜 f a = 0
    · simp only [h, inner_zero_left, zero_div, zero_mul, sub_zero]
    · rw [RCLike.ofReal_pow, ← inner_self_eq_norm_sq_to_K, div_mul_cancel₀, sub_self]
      rwa [inner_self_ne_zero]
  intro i hi hia
  simp only [mul_eq_zero, div_eq_zero_iff, inner_self_eq_zero]
  right
  cases' hia.lt_or_lt with hia₁ hia₂
  · rw [inner_eq_zero_symm]
    exact ih a h₀ i hia₁
  · exact ih i (mem_Iio.1 hi) a hia₂
#align gram_schmidt_orthogonal gramSchmidt_orthogonal

def 𝕜 f i]
  simp_rw [orthogonalProjection_singleton]
  refine' Submodule.sub_mem _ (subset_span (mem_image_of_mem _ hij))
    (Submodule.sum_mem _ fun k hk => _)
  let hkj : k < j := (Finset.mem_Iio.1 hk).trans_le hij
  exact smul_mem _ _
    (span_mono (image_subset f <| Iic_subset_Iic.2 hkj.le) <| gramSchmidt_mem_span _ le_rfl)
termination_by j => j
#align gram_schmidt_mem_span gramSchmidt_mem_span

def gramSchmidtBasis (b : Basis ι 𝕜 E) : Basis ι 𝕜 E :=
  Basis.mk (gramSchmidt_linearIndependent b.linearIndependent)
    ((span_gramSchmidt 𝕜 b).trans b.span_eq).ge
#align gram_schmidt_basis gramSchmidtBasis

def gramSchmidtNormed (f : ι → E) (n : ι) : E :=
  (‖gramSchmidt 𝕜 f n‖ : 𝕜)⁻¹ • gramSchmidt 𝕜 f n
#align gram_schmidt_normed gramSchmidtNormed

def gramSchmidtOrthonormalBasis : OrthonormalBasis ι 𝕜 E :=
  ((gramSchmidt_orthonormal' f).exists_orthonormalBasis_extension_of_card_eq
    (v := gramSchmidtNormed 𝕜 f) h).choose
#align gram_schmidt_orthonormal_basis gramSchmidtOrthonormalBasis