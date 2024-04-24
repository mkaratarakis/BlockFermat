def applyComposition (p : FormalMultilinearSeries 𝕜 E F) {n : ℕ} (c : Composition n) :
    (Fin n → E) → Fin c.length → F := fun v i => p (c.blocksFun i) (v ∘ c.embedding i)
#align formal_multilinear_series.apply_composition FormalMultilinearSeries.applyComposition

def compAlongComposition {n : ℕ} (p : FormalMultilinearSeries 𝕜 E F) (c : Composition n)
    (f : ContinuousMultilinearMap 𝕜 (fun _i : Fin c.length => F) G) :
    ContinuousMultilinearMap 𝕜 (fun _i : Fin n => E) G where
  toFun v := f (p.applyComposition c v)
  map_add' v i x y := by
    cases Subsingleton.elim ‹_› (instDecidableEqFin _)
    simp only [applyComposition_update, ContinuousMultilinearMap.map_add]
  map_smul' v i c x := by
    cases Subsingleton.elim ‹_› (instDecidableEqFin _)
    simp only [applyComposition_update, ContinuousMultilinearMap.map_smul]
  cont :=
    f.cont.comp <|
      continuous_pi fun i => (coe_continuous _).comp <| continuous_pi fun j => continuous_apply _
#align continuous_multilinear_map.comp_along_composition ContinuousMultilinearMap.compAlongComposition

def compAlongComposition {n : ℕ} (q : FormalMultilinearSeries 𝕜 F G)
    (p : FormalMultilinearSeries 𝕜 E F) (c : Composition n) :
    ContinuousMultilinearMap 𝕜 (fun _i : Fin n => E) G :=
  (q c.length).compAlongComposition p c
#align formal_multilinear_series.comp_along_composition FormalMultilinearSeries.compAlongComposition

def comp (q : FormalMultilinearSeries 𝕜 F G) (p : FormalMultilinearSeries 𝕜 E F) :
    FormalMultilinearSeries 𝕜 E G := fun n => ∑ c : Composition n, q.compAlongComposition p c
#align formal_multilinear_series.comp FormalMultilinearSeries.comp

def id : FormalMultilinearSeries 𝕜 E E
  | 0 => 0
  | 1 => (continuousMultilinearCurryFin1 𝕜 E E).symm (ContinuousLinearMap.id 𝕜 E)
  | _ => 0
#align formal_multilinear_series.id FormalMultilinearSeries.id

def compPartialSumSource (m M N : ℕ) : Finset (Σ n, Fin n → ℕ) :=
  Finset.sigma (Finset.Ico m M) (fun n : ℕ => Fintype.piFinset fun _i : Fin n => Finset.Ico 1 N : _)
#align formal_multilinear_series.comp_partial_sum_source FormalMultilinearSeries.compPartialSumSource

def compChangeOfVariables (m M N : ℕ) (i : Σ n, Fin n → ℕ) (hi : i ∈ compPartialSumSource m M N) :
    Σ n, Composition n := by
  rcases i with ⟨n, f⟩
  rw [mem_compPartialSumSource_iff] at hi
  refine' ⟨∑ j, f j, ofFn fun a => f a, fun hi' => _, by simp [sum_ofFn]⟩
  rename_i i
  obtain ⟨j, rfl⟩ : ∃ j : Fin n, f j = i := by rwa [mem_ofFn, Set.mem_range] at hi'
  exact (hi.2 j).1
#align formal_multilinear_series.comp_change_of_variables FormalMultilinearSeries.compChangeOfVariables

def compPartialSumTargetSet (m M N : ℕ) : Set (Σ n, Composition n) :=
  {i | m ≤ i.2.length ∧ i.2.length < M ∧ ∀ j : Fin i.2.length, i.2.blocksFun j < N}
#align formal_multilinear_series.comp_partial_sum_target_set FormalMultilinearSeries.compPartialSumTargetSet

def compPartialSumTarget (m M N : ℕ) : Finset (Σ n, Composition n) :=
  Set.Finite.toFinset <|
    ((Finset.finite_toSet _).dependent_image _).subset <|
      compPartialSumTargetSet_image_compPartialSumSource m M N
#align formal_multilinear_series.comp_partial_sum_target FormalMultilinearSeries.compPartialSumTarget

def gather (a : Composition n) (b : Composition a.length) : Composition n where
  blocks := (a.blocks.splitWrtComposition b).map sum
  blocks_pos := by
    rw [forall_mem_map_iff]
    intro j hj
    suffices H : ∀ i ∈ j, 1 ≤ i by calc
      0 < j.length := length_pos_of_mem_splitWrtComposition hj
      _ ≤ j.sum := length_le_sum_of_one_le _ H
    intro i hi
    apply a.one_le_blocks
    rw [← a.blocks.join_splitWrtComposition b]
    exact mem_join_of_mem hj hi
  blocks_sum := by rw [← sum_join, join_splitWrtComposition, a.blocks_sum]
#align composition.gather Composition.gather

def sigmaCompositionAux (a : Composition n) (b : Composition a.length)
    (i : Fin (a.gather b).length) : Composition ((a.gather b).blocksFun i) where
  blocks :=
    List.get (a.blocks.splitWrtComposition b)
      ⟨i.val, (by rw [length_splitWrtComposition, ← length_gather]; exact i.2)⟩
  blocks_pos {i} hi :=
    a.blocks_pos
      (by
        rw [← a.blocks.join_splitWrtComposition b]
        exact mem_join_of_mem (List.get_mem _ _ _) hi)
  blocks_sum := by simp only [Composition.blocksFun, get_map, Composition.gather]
#align composition.sigma_composition_aux Composition.sigmaCompositionAux

def sigmaEquivSigmaPi (n : ℕ) :
    (Σ a : Composition n, Composition a.length) ≃
      Σ c : Composition n, ∀ i : Fin c.length, Composition (c.blocksFun i) where
  toFun i := ⟨i.1.gather i.2, i.1.sigmaCompositionAux i.2⟩
  invFun i :=
    ⟨{  blocks := (ofFn fun j => (i.2 j).blocks).join
        blocks_pos := by
          simp only [and_imp, List.mem_join, exists_imp, forall_mem_ofFn_iff]
          exact @fun i j hj => Composition.blocks_pos _ hj
        blocks_sum := by simp [sum_ofFn, Composition.blocks_sum, Composition.sum_blocksFun] },
      { blocks := ofFn fun j => (i.2 j).length
        blocks_pos := by
          intro k hk
          refine' ((forall_mem_ofFn_iff (P := fun i => 0 < i)).2 fun j => _) k hk
          exact Composition.length_pos_of_pos _ (Composition.blocks_pos' _ _ _)
        blocks_sum := by dsimp only [Composition.length]; simp [sum_ofFn] }⟩
  left_inv := by
    -- the fact that we have a left inverse is essentially `join_split_wrt_composition`,
    -- but we need to massage it to take care of the dependent setting.
    rintro ⟨a, b⟩
    rw [sigma_composition_eq_iff]
    dsimp
    constructor
    · conv_rhs =>
        rw [← join_splitWrtComposition a.blocks b, ← ofFn_get (splitWrtComposition a.blocks b)]
      have A : length (gather a b) = List.length (splitWrtComposition a.blocks b) := by
        simp only [length, gather, length_map, length_splitWrtComposition]
      congr! 2
      · exact (Fin.heq_fun_iff A (α := List ℕ)).2 fun i => rfl
    · have B : Composition.length (Composition.gather a b) = List.length b.blocks :=
        Composition.length_gather _ _
      conv_rhs => rw [← ofFn_get b.blocks]
      congr 1
      refine' (Fin.heq_fun_iff B).2 fun i => _
      rw [sigmaCompositionAux, Composition.length, List.get_map_rev List.length,
        List.get_of_eq (map_length_splitWrtComposition _ _)]
  right_inv := by
    -- the fact that we have a right inverse is essentially `splitWrtComposition_join`,
    -- but we need to massage it to take care of the dependent setting.
    rintro ⟨c, d⟩
    have : map List.sum (ofFn fun i : Fin (Composition.length c) => (d i).blocks) = c.blocks := by
      simp [map_ofFn, (· ∘ ·), Composition.blocks_sum, Composition.ofFn_blocksFun]
    rw [sigma_pi_composition_eq_iff]
    dsimp
    congr! 1
    · congr
      ext1
      dsimp [Composition.gather]
      rwa [splitWrtComposition_join]
      simp only [map_ofFn]
      rfl
    · rw [Fin.heq_fun_iff]
      intro i
      dsimp [Composition.sigmaCompositionAux]
      rw [get_of_eq (splitWrtComposition_join _ _ _)]
      · simp only [get_ofFn]
        rfl
      · simp only [map_ofFn]
        rfl
      · congr
#align composition.sigma_equiv_sigma_pi Composition.sigmaEquivSigmaPi