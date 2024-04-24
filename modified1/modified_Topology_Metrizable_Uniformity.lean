def ofPreNNDist (d : X → X → ℝ≥0) (dist_self : ∀ x, d x x = 0)
    (dist_comm : ∀ x y, d x y = d y x) : PseudoMetricSpace X where
  dist x y := ↑(⨅ l : List X, ((x::l).zipWith d (l ++ [y])).sum : ℝ≥0)
  dist_self x := NNReal.coe_eq_zero.2 <|
      nonpos_iff_eq_zero.1 <| (ciInf_le (OrderBot.bddBelow _) []).trans_eq <| by simp [dist_self]
  dist_comm x y :=
    NNReal.coe_inj.2 <| by
      refine' reverse_surjective.iInf_congr _ fun l => _
      rw [← sum_reverse, zipWith_distrib_reverse, reverse_append, reverse_reverse,
        reverse_singleton, singleton_append, reverse_cons, reverse_reverse,
        zipWith_comm_of_comm _ dist_comm]
      simp only [length, length_append]
  dist_triangle x y z := by
    -- Porting note: added `unfold`
    unfold dist
    rw [← NNReal.coe_add, NNReal.coe_le_coe]
    refine' NNReal.le_iInf_add_iInf fun lxy lyz => _
    calc
      ⨅ l, (zipWith d (x::l) (l ++ [z])).sum ≤
          (zipWith d (x::lxy ++ y::lyz) ((lxy ++ y::lyz) ++ [z])).sum :=
        ciInf_le (OrderBot.bddBelow _) (lxy ++ y::lyz)
      _ = (zipWith d (x::lxy) (lxy ++ [y])).sum + (zipWith d (y::lyz) (lyz ++ [z])).sum := by
        rw [← sum_append, ← zipWith_append, cons_append, ← @singleton_append _ y, append_assoc,
          append_assoc, append_assoc]
        rw [length_cons, length_append, length_singleton]
  -- Porting note: `edist_dist` is no longer inferred
  edist_dist x y := rfl
#align pseudo_metric_space.of_prenndist PseudoMetricSpace.ofPreNNDist

def UniformSpace.pseudoMetricSpace (X : Type*) [UniformSpace X]
    [IsCountablyGenerated (𝓤 X)] : PseudoMetricSpace X :=
  (UniformSpace.metrizable_uniformity X).choose.replaceUniformity <|
    congr_arg _ (UniformSpace.metrizable_uniformity X).choose_spec.symm
#align uniform_space.pseudo_metric_space UniformSpace.pseudoMetricSpace

def UniformSpace.metricSpace (X : Type*) [UniformSpace X]
    [IsCountablyGenerated (𝓤 X)] [T0Space X] : MetricSpace X :=
  @MetricSpace.ofT0PseudoMetricSpace X (UniformSpace.pseudoMetricSpace X) _
#align uniform_space.metric_space UniformSpace.metricSpace

structure that generates the same uniformity.
The proof follows [Sergey Melikhov, Metrizable uniform spaces][melikhov2011].

## Main definitions

structure such that
  `NNDist x y ≤ d x y` for all `x y : X`.

* `UniformSpace.pseudoMetricSpace`: given a uniform space `X` with countably generated `𝓤 X`,
  constructs a `PseudoMetricSpace X` instance that is compatible with the uniform space structure.

* `UniformSpace.metricSpace`: given a T₀ uniform space `X` with countably generated `𝓤 X`,
  constructs a `MetricSpace X` instance that is compatible with the uniform space structure.

## Main statements

structure that is compatible with this `UniformSpace`
  structure. Use `UniformSpace.pseudoMetricSpace` or `UniformSpace.metricSpace` instead.

* `UniformSpace.pseudoMetrizableSpace`: a uniform space with countably generated `𝓤 X` is pseudo
  metrizable.

* `UniformSpace.metrizableSpace`: a T₀ uniform space with countably generated `𝓤 X` is
  metrizable. This is not an instance to avoid loops.

## Tags

structure on `X` such that `dist x y ≤ d x y` for all `x y`,
where `d : X → X → ℝ≥0` is a function such that `d x x = 0` and `d x y = d y x` for all `x`, `y`. -/
noncomputable def ofPreNNDist (d : X → X → ℝ≥0) (dist_self : ∀ x, d x x = 0)
    (dist_comm : ∀ x y, d x y = d y x) : PseudoMetricSpace X where
  dist x y := ↑(⨅ l : List X, ((x::l).zipWith d (l ++ [y])).sum : ℝ≥0)
  dist_self x := NNReal.coe_eq_zero.2 <|
      nonpos_iff_eq_zero.1 <| (ciInf_le (OrderBot.bddBelow _) []).trans_eq <| by simp [dist_self]
  dist_comm x y :=
    NNReal.coe_inj.2 <| by
      refine' reverse_surjective.iInf_congr _ fun l => _
      rw [← sum_reverse, zipWith_distrib_reverse, reverse_append, reverse_reverse,
        reverse_singleton, singleton_append, reverse_cons, reverse_reverse,
        zipWith_comm_of_comm _ dist_comm]
      simp only [length, length_append]
  dist_triangle x y z := by
    -- Porting note: added `unfold`
    unfold dist
    rw [← NNReal.coe_add, NNReal.coe_le_coe]
    refine' NNReal.le_iInf_add_iInf fun lxy lyz => _
    calc
      ⨅ l, (zipWith d (x::l) (l ++ [z])).sum ≤
          (zipWith d (x::lxy ++ y::lyz) ((lxy ++ y::lyz) ++ [z])).sum :=
        ciInf_le (OrderBot.bddBelow _) (lxy ++ y::lyz)
      _ = (zipWith d (x::lxy) (lxy ++ [y])).sum + (zipWith d (y::lyz) (lyz ++ [z])).sum := by
        rw [← sum_append, ← zipWith_append, cons_append, ← @singleton_append _ y, append_assoc,
          append_assoc, append_assoc]
        rw [length_cons, length_append, length_singleton]
  -- Porting note: `edist_dist` is no longer inferred
  edist_dist x y := rfl
#align pseudo_metric_space.of_prenndist PseudoMetricSpace.ofPreNNDist

structure compatible with the `UniformSpace` structure. Use
`UniformSpace.pseudoMetricSpace` or `UniformSpace.metricSpace` instead. -/
protected theorem UniformSpace.metrizable_uniformity (X : Type*) [UniformSpace X]
    [IsCountablyGenerated (𝓤 X)] : ∃ I : PseudoMetricSpace X, I.toUniformSpace = ‹_› := by
  classical
  /- Choose a fast decreasing antitone basis `U : ℕ → set (X × X)` of the uniformity filter `𝓤 X`.
    Define `d x y : ℝ≥0` to be `(1 / 2) ^ n`, where `n` is the minimal index of `U n` that
    separates `x` and `y`: `(x, y) ∉ U n`, or `0` if `x` is not separated from `y`. This function
    satisfies the assumptions of `PseudoMetricSpace.ofPreNNDist` and
    `PseudoMetricSpace.le_two_mul_dist_ofPreNNDist`, hence the distance given by the former pseudo
    metric space structure is Lipschitz equivalent to the `d`. Thus the uniformities generated by
    `d` and `dist` are equal. Since the former uniformity is equal to `𝓤 X`, the latter is equal to
    `𝓤 X` as well. -/
  obtain ⟨U, hU_symm, hU_comp, hB⟩ :
    ∃ U : ℕ → Set (X × X),
      (∀ n, SymmetricRel (U n)) ∧
        (∀ ⦃m n⦄, m < n → U n ○ (U n ○ U n) ⊆ U m) ∧ (𝓤 X).HasAntitoneBasis U := by
    rcases UniformSpace.has_seq_basis X with ⟨V, hB, hV_symm⟩
    rcases hB.subbasis_with_rel fun m =>
        hB.tendsto_smallSets.eventually
          (eventually_uniformity_iterate_comp_subset (hB.mem m) 2) with
      ⟨φ, -, hφ_comp, hφB⟩
    exact ⟨V ∘ φ, fun n => hV_symm _, hφ_comp, hφB⟩
  set d : X → X → ℝ≥0 := fun x y => if h : ∃ n, (x, y) ∉ U n then (1 / 2) ^ Nat.find h else 0
  have hd₀ : ∀ {x y}, d x y = 0 ↔ Inseparable x y := by
    intro x y
    refine' Iff.trans _ hB.inseparable_iff_uniformity.symm
    simp only [d, true_imp_iff]
    split_ifs with h
    · rw [← not_forall] at h
      simp [h, pow_eq_zero_iff']
    · simpa only [not_exists, Classical.not_not, eq_self_iff_true, true_iff_iff] using h
  have hd_symm : ∀ x y, d x y = d y x := by
    intro x y
    simp only [d, @SymmetricRel.mk_mem_comm _ _ (hU_symm _) x y]
  have hr : (1 / 2 : ℝ≥0) ∈ Ioo (0 : ℝ≥0) 1 := ⟨half_pos one_pos, NNReal.half_lt_self one_ne_zero⟩
  letI I := PseudoMetricSpace.ofPreNNDist d (fun x => hd₀.2 rfl) hd_symm
  have hdist_le : ∀ x y, dist x y ≤ d x y := PseudoMetricSpace.dist_ofPreNNDist_le _ _ _
  have hle_d : ∀ {x y : X} {n : ℕ}, (1 / 2) ^ n ≤ d x y ↔ (x, y) ∉ U n := by
    intro x y n
    dsimp only [d]
    split_ifs with h
    · rw [(pow_right_strictAnti hr.1 hr.2).le_iff_le, Nat.find_le_iff]
      exact ⟨fun ⟨m, hmn, hm⟩ hn => hm (hB.antitone hmn hn), fun h => ⟨n, le_rfl, h⟩⟩
    · push_neg at h
      simp only [h, not_true, (pow_pos hr.1 _).not_le]
  have hd_le : ∀ x y, ↑(d x y) ≤ 2 * dist x y := by
    refine' PseudoMetricSpace.le_two_mul_dist_ofPreNNDist _ _ _ fun x₁ x₂ x₃ x₄ => _
    by_cases H : ∃ n, (x₁, x₄) ∉ U n
    · refine' (dif_pos H).trans_le _
      rw [← NNReal.div_le_iff' two_ne_zero, ← mul_one_div (_ ^ _), ← pow_succ]
      simp only [le_max_iff, hle_d, ← not_and_or]
      rintro ⟨h₁₂, h₂₃, h₃₄⟩
      refine' Nat.find_spec H (hU_comp (lt_add_one <| Nat.find H) _)
      exact ⟨x₂, h₁₂, x₃, h₂₃, h₃₄⟩
    · exact (dif_neg H).trans_le (zero_le _)
  -- Porting note: without the next line, `uniformity_basis_dist_pow` ends up introducing some
  -- `Subtype.val` applications instead of `NNReal.toReal`.
  rw [mem_Ioo, ← NNReal.coe_lt_coe, ← NNReal.coe_lt_coe] at hr
  refine' ⟨I, UniformSpace.ext <| (uniformity_basis_dist_pow hr.1 hr.2).ext hB.toHasBasis _ _⟩
  · refine' fun n hn => ⟨n, hn, fun x hx => (hdist_le _ _).trans_lt _⟩
    rwa [← NNReal.coe_pow, NNReal.coe_lt_coe, ← not_le, hle_d, Classical.not_not]
  · refine' fun n _ => ⟨n + 1, trivial, fun x hx => _⟩
    rw [mem_setOf_eq] at hx
    contrapose! hx
    refine' le_trans _ ((div_le_iff' (zero_lt_two' ℝ)).2 (hd_le x.1 x.2))
    rwa [← NNReal.coe_two, ← NNReal.coe_div, ← NNReal.coe_pow, NNReal.coe_le_coe, pow_succ,
      mul_one_div, NNReal.div_le_iff two_ne_zero, div_mul_cancel₀ _ (two_ne_zero' ℝ≥0), hle_d]
#align uniform_space.metrizable_uniformity UniformSpace.metrizable_uniformity