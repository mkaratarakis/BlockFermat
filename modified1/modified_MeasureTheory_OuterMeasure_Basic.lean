def coeFnAddMonoidHom : OuterMeasure α →+ Set α → ℝ≥0∞ where
  toFun := (⇑)
  map_zero' := coe_zero
  map_add' := coe_add
#align measure_theory.outer_measure.coe_fn_add_monoid_hom MeasureTheory.OuterMeasure.coeFnAddMonoidHom

def map {β} (f : α → β) : OuterMeasure α →ₗ[ℝ≥0∞] OuterMeasure β where
  toFun m :=
    { measureOf := fun s => m (f ⁻¹' s)
      empty := m.empty
      mono := fun {s t} h => m.mono (preimage_mono h)
      iUnion_nat := fun s => by simp; apply m.iUnion_nat fun i => f ⁻¹' s i }
  map_add' m₁ m₂ := coe_fn_injective rfl
  map_smul' c m := coe_fn_injective rfl
#align measure_theory.outer_measure.map MeasureTheory.OuterMeasure.map

def dirac (a : α) : OuterMeasure α where
  measureOf s := indicator s (fun _ => 1) a
  empty := by simp
  mono {s t} h := indicator_le_indicator_of_subset h (fun _ => zero_le _) a
  iUnion_nat s :=
    if hs : a ∈ ⋃ n, s n then
      let ⟨i, hi⟩ := mem_iUnion.1 hs
      calc
        indicator (⋃ n, s n) (fun _ => (1 : ℝ≥0∞)) a = 1 := indicator_of_mem hs _
        _ = indicator (s i) (fun _ => 1) a := Eq.symm (indicator_of_mem hi _)
        _ ≤ ∑' n, indicator (s n) (fun _ => 1) a := ENNReal.le_tsum _

    else by simp only [indicator_of_not_mem hs, zero_le]
#align measure_theory.outer_measure.dirac MeasureTheory.OuterMeasure.dirac

def sum {ι} (f : ι → OuterMeasure α) : OuterMeasure α where
  measureOf s := ∑' i, f i s
  empty := by simp
  mono {s t} h := ENNReal.tsum_le_tsum fun i => (f i).mono' h
  iUnion_nat s := by
    rw [ENNReal.tsum_comm]; exact ENNReal.tsum_le_tsum fun i => (f i).iUnion_nat _
#align measure_theory.outer_measure.sum MeasureTheory.OuterMeasure.sum

def comap {β} (f : α → β) : OuterMeasure β →ₗ[ℝ≥0∞] OuterMeasure α where
  toFun m :=
    { measureOf := fun s => m (f '' s)
      empty := by simp
      mono := fun {s t} h => m.mono <| image_subset f h
      iUnion_nat := fun s => by
        simp only
        rw [image_iUnion]
        apply m.iUnion_nat }
  map_add' m₁ m₂ := rfl
  map_smul' c m := rfl
#align measure_theory.outer_measure.comap MeasureTheory.OuterMeasure.comap

def restrict (s : Set α) : OuterMeasure α →ₗ[ℝ≥0∞] OuterMeasure α :=
  (map (↑)).comp (comap ((↑) : s → α))
#align measure_theory.outer_measure.restrict MeasureTheory.OuterMeasure.restrict

def ofFunction : OuterMeasure α :=
  let μ s := ⨅ (f : ℕ → Set α) (_ : s ⊆ ⋃ i, f i), ∑' i, m (f i)
  { measureOf := μ
    empty :=
      le_antisymm
        ((iInf_le_of_le fun _ => ∅) <| iInf_le_of_le (empty_subset _) <| by simp [m_empty])
        (zero_le _)
    mono := fun {s₁ s₂} hs => iInf_mono fun f => iInf_mono' fun hb => ⟨hs.trans hb, le_rfl⟩
    iUnion_nat := fun s =>
      ENNReal.le_of_forall_pos_le_add <| by
        intro ε hε (hb : (∑' i, μ (s i)) < ∞)
        rcases ENNReal.exists_pos_sum_of_countable (ENNReal.coe_pos.2 hε).ne' ℕ with ⟨ε', hε', hl⟩
        refine' le_trans _ (add_le_add_left (le_of_lt hl) _)
        rw [← ENNReal.tsum_add]
        choose f hf using
          show ∀ i, ∃ f : ℕ → Set α, (s i ⊆ ⋃ i, f i) ∧ (∑' i, m (f i)) < μ (s i) + ε' i by
            intro i
            have : μ (s i) < μ (s i) + ε' i :=
              ENNReal.lt_add_right (ne_top_of_le_ne_top hb.ne <| ENNReal.le_tsum _)
                (by simpa using (hε' i).ne')
            rcases iInf_lt_iff.mp this with ⟨t, ht⟩
            exists t
            contrapose! ht
            exact le_iInf ht
        refine' le_trans _ (ENNReal.tsum_le_tsum fun i => le_of_lt (hf i).2)
        rw [← ENNReal.tsum_prod, ← Nat.pairEquiv.symm.tsum_eq]
        refine' iInf_le_of_le _ (iInf_le _ _)
        apply iUnion_subset
        intro i
        apply Subset.trans (hf i).1
        apply iUnion_subset
        simp only [Nat.pairEquiv_symm_apply]
        rw [iUnion_unpair]
        intro j
        apply subset_iUnion₂ i }
#align measure_theory.outer_measure.of_function MeasureTheory.OuterMeasure.ofFunction

def boundedBy : OuterMeasure α :=
  OuterMeasure.ofFunction (fun s => ⨆ _ : s.Nonempty, m s) (by simp [Set.not_nonempty_empty])
#align measure_theory.outer_measure.bounded_by MeasureTheory.OuterMeasure.boundedBy

def IsCaratheodory (s : Set α) : Prop :=
  ∀ t, m t = m (t ∩ s) + m (t \ s)
#align measure_theory.outer_measure.is_caratheodory MeasureTheory.OuterMeasure.IsCaratheodory

def caratheodoryDynkin : MeasurableSpace.DynkinSystem α where
  Has := IsCaratheodory m
  has_empty := isCaratheodory_empty m
  has_compl s := isCaratheodory_compl m s
  has_iUnion_nat f hf hn := by apply isCaratheodory_iUnion_nat m hf f
#align measure_theory.outer_measure.caratheodory_dynkin MeasureTheory.OuterMeasure.caratheodoryDynkin

def caratheodory : MeasurableSpace α := by
  apply MeasurableSpace.DynkinSystem.toMeasurableSpace (caratheodoryDynkin m)
  intro s₁ s₂
  apply isCaratheodory_inter
#align measure_theory.outer_measure.caratheodory MeasureTheory.OuterMeasure.caratheodory

def sInfGen (m : Set (OuterMeasure α)) (s : Set α) : ℝ≥0∞ :=
  ⨅ (μ : OuterMeasure α) (_ : μ ∈ m), μ s
#align measure_theory.outer_measure.Inf_gen MeasureTheory.OuterMeasure.sInfGen

def (m : Set (OuterMeasure α)) (t : Set α) :
    sInfGen m t = ⨅ (μ : OuterMeasure α) (_ : μ ∈ m), μ t :=
  rfl
#align measure_theory.outer_measure.Inf_gen_def MeasureTheory.OuterMeasure.sInfGen_def

def extend (s : α) : ℝ≥0∞ :=
  ⨅ h : P s, m s h
#align measure_theory.extend MeasureTheory.extend

def inducedOuterMeasure : OuterMeasure α :=
  OuterMeasure.ofFunction (extend m) (extend_empty P0 m0)
#align measure_theory.induced_outer_measure MeasureTheory.inducedOuterMeasure

def trim : OuterMeasure α :=
  inducedOuterMeasure (fun s _ => m s) MeasurableSet.empty m.empty
#align measure_theory.outer_measure.trim MeasureTheory.OuterMeasure.trim

structure OuterMeasure (α : Type*) where
  measureOf : Set α → ℝ≥0∞
  empty : measureOf ∅ = 0
  mono : ∀ {s₁ s₂}, s₁ ⊆ s₂ → measureOf s₁ ≤ measureOf s₂
  iUnion_nat : ∀ s : ℕ → Set α, measureOf (⋃ i, s i) ≤ ∑' i, measureOf (s i)
#align measure_theory.outer_measure MeasureTheory.OuterMeasure