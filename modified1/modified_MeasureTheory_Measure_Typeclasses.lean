def measureUnivNNReal (μ : Measure α) : ℝ≥0 :=
  (μ univ).toNNReal
#align measure_theory.measure_univ_nnreal MeasureTheory.measureUnivNNReal

def FiniteAtFilter {_m0 : MeasurableSpace α} (μ : Measure α) (f : Filter α) : Prop :=
  ∃ s ∈ f, μ s < ∞
#align measure_theory.measure.finite_at_filter MeasureTheory.Measure.FiniteAtFilter

def sFiniteSeq (μ : Measure α) [h : SFinite μ] : ℕ → Measure α := h.1.choose

instance isFiniteMeasure_sFiniteSeq [h : SFinite μ] (n : ℕ) : IsFiniteMeasure (sFiniteSeq μ n) :=
  h.1.choose_spec.1 n

lemma sum_sFiniteSeq (μ : Measure α) [h : SFinite μ] : sum (sFiniteSeq μ) = μ :=
  h.1.choose_spec.2.symm

/-- A countable sum of finite measures is s-finite.
This lemma is superseeded by the instance below. -/
lemma sfinite_sum_of_countable {ι : Type*} [Countable ι]
    (m : ι → Measure α) [∀ n, IsFiniteMeasure (m n)] : SFinite (Measure.sum m) := by
  classical
  obtain ⟨f, hf⟩ : ∃ f : ι → ℕ, Function.Injective f := Countable.exists_injective_nat ι
  refine ⟨_, fun n ↦ ?_, (sum_extend_zero hf m).symm⟩
  rcases em (n ∈ range f) with ⟨i, rfl⟩ | hn
  · rw [hf.extend_apply]
    infer_instance
  · rw [Function.extend_apply' _ _ _ hn, Pi.zero_apply]
    infer_instance

instance {ι : Type*} [Countable ι] (m : ι → Measure α) [∀ n, SFinite (m n)] :
    SFinite (Measure.sum m) := by
  change SFinite (Measure.sum (fun i ↦ m i))
  simp_rw [← sum_sFiniteSeq (m _), Measure.sum_sum]
  apply sfinite_sum_of_countable

end SFinite

/-- A measure `μ` is called σ-finite if there is a countable collection of sets
 `{ A i | i ∈ ℕ }` such that `μ (A i) < ∞` and `⋃ i, A i = s`. -/
class SigmaFinite {m0 : MeasurableSpace α} (μ : Measure α) : Prop where
  out' : Nonempty (μ.FiniteSpanningSetsIn univ)
#align measure_theory.sigma_finite MeasureTheory.SigmaFinite

def Measure.toFiniteSpanningSetsIn (μ : Measure α) [h : SigmaFinite μ] :
    μ.FiniteSpanningSetsIn { s | MeasurableSet s } where
  set n := toMeasurable μ (h.out.some.set n)
  set_mem n := measurableSet_toMeasurable _ _
  finite n := by
    rw [measure_toMeasurable]
    exact h.out.some.finite n
  spanning := eq_univ_of_subset (iUnion_mono fun n => subset_toMeasurable _ _) h.out.some.spanning
#align measure_theory.measure.to_finite_spanning_sets_in MeasureTheory.Measure.toFiniteSpanningSetsIn

def spanningSets (μ : Measure α) [SigmaFinite μ] (i : ℕ) : Set α :=
  Accumulate μ.toFiniteSpanningSetsIn.set i
#align measure_theory.spanning_sets MeasureTheory.spanningSets

def spanningSetsIndex (μ : Measure α) [SigmaFinite μ] (x : α) : ℕ :=
  Nat.find <| iUnion_eq_univ_iff.1 (iUnion_spanningSets μ) x
#align measure_theory.spanning_sets_index MeasureTheory.spanningSetsIndex

def
  rcases exists_seq_strictAnti_tendsto' (zero_lt_one : (0 : ℝ≥0∞) < 1) with
    ⟨as, _, as_mem, as_lim⟩
  set fairmeas := fun n : ℕ => { i : ι | as n ≤ μ (As i) }
  have countable_union : posmeas = ⋃ n, fairmeas n := by
    have fairmeas_eq : ∀ n, fairmeas n = (fun i => μ (As i)) ⁻¹' Ici (as n) := fun n => by
      simp only [fairmeas]
      rfl
    simpa only [fairmeas_eq, posmeas_def, ← preimage_iUnion,
      iUnion_Ici_eq_Ioi_of_lt_of_tendsto (0 : ℝ≥0∞) (fun n => (as_mem n).1) as_lim]
  rw [countable_union]
  refine' countable_iUnion fun n => Finite.countable _
  exact finite_const_le_meas_of_disjoint_iUnion₀ μ (as_mem n).1 As_mble As_disj Union_As_finite

/-- If the union of disjoint measurable sets has finite measure, then there are only
countably many members of the union whose measure is positive. -/
theorem countable_meas_pos_of_disjoint_of_meas_iUnion_ne_top {ι : Type*} {_ : MeasurableSpace α}
    (μ : Measure α) {As : ι → Set α} (As_mble : ∀ i : ι, MeasurableSet (As i))
    (As_disj : Pairwise (Disjoint on As)) (Union_As_finite : μ (⋃ i, As i) ≠ ∞) :
    Set.Countable { i : ι | 0 < μ (As i) } :=
  countable_meas_pos_of_disjoint_of_meas_iUnion_ne_top₀ μ (fun i ↦ (As_mble i).nullMeasurableSet)
    ((fun _ _ h ↦ Disjoint.aedisjoint (As_disj h))) Union_As_finite
#align measure_theory.measure.countable_meas_pos_of_disjoint_of_meas_Union_ne_top MeasureTheory.Measure.countable_meas_pos_of_disjoint_of_meas_iUnion_ne_top

def mono' (h : μ.FiniteSpanningSetsIn C) (hC : C ∩ { s | μ s < ∞ } ⊆ D) :
    μ.FiniteSpanningSetsIn D :=
  ⟨h.set, fun i => hC ⟨h.set_mem i, h.finite i⟩, h.finite, h.spanning⟩
#align measure_theory.measure.finite_spanning_sets_in.mono' MeasureTheory.Measure.FiniteSpanningSetsIn.mono'

def mono (h : μ.FiniteSpanningSetsIn C) (hC : C ⊆ D) : μ.FiniteSpanningSetsIn D :=
  h.mono' fun _s hs => hC hs.1
#align measure_theory.measure.finite_spanning_sets_in.mono MeasureTheory.Measure.FiniteSpanningSetsIn.mono

def FiniteSpanningSetsIn.ofLE (h : ν ≤ μ) {C : Set (Set α)} (S : μ.FiniteSpanningSetsIn C) :
    ν.FiniteSpanningSetsIn C where
  set := S.set
  set_mem := S.set_mem
  finite n := lt_of_le_of_lt (le_iff'.1 h _) (S.finite n)
  spanning := S.spanning
#align measure_theory.measure.finite_spanning_sets_in.of_le MeasureTheory.Measure.FiniteSpanningSetsIn.ofLE

def FiniteSpanningSetsIn.disjointed {μ : Measure α}
    (S : μ.FiniteSpanningSetsIn { s | MeasurableSet s }) :
    μ.FiniteSpanningSetsIn { s | MeasurableSet s } :=
  ⟨disjointed S.set, MeasurableSet.disjointed S.set_mem, fun n =>
    lt_of_le_of_lt (measure_mono (disjointed_subset S.set n)) (S.finite _),
    S.spanning ▸ iUnion_disjointed⟩
#align measure_theory.measure.finite_spanning_sets_in.disjointed MeasureTheory.Measure.FiniteSpanningSetsIn.disjointed

def MeasureTheory.Measure.finiteSpanningSetsInCompact [TopologicalSpace α] [SigmaCompactSpace α]
    {_ : MeasurableSpace α} (μ : Measure α) [IsLocallyFiniteMeasure μ] :
    μ.FiniteSpanningSetsIn { K | IsCompact K } where
  set := compactCovering α
  set_mem := isCompact_compactCovering α
  finite n := (isCompact_compactCovering α n).measure_lt_top
  spanning := iUnion_compactCovering α
#align measure_theory.measure.finite_spanning_sets_in_compact MeasureTheory.Measure.finiteSpanningSetsInCompact

def MeasureTheory.Measure.finiteSpanningSetsInOpen [TopologicalSpace α] [SigmaCompactSpace α]
    {_ : MeasurableSpace α} (μ : Measure α) [IsLocallyFiniteMeasure μ] :
    μ.FiniteSpanningSetsIn { K | IsOpen K } where
  set n := ((isCompact_compactCovering α n).exists_open_superset_measure_lt_top μ).choose
  set_mem n :=
    ((isCompact_compactCovering α n).exists_open_superset_measure_lt_top μ).choose_spec.2.1
  finite n :=
    ((isCompact_compactCovering α n).exists_open_superset_measure_lt_top μ).choose_spec.2.2
  spanning :=
    eq_univ_of_subset
      (iUnion_mono fun n =>
        ((isCompact_compactCovering α n).exists_open_superset_measure_lt_top μ).choose_spec.1)
      (iUnion_compactCovering α)
#align measure_theory.measure.finite_spanning_sets_in_open MeasureTheory.Measure.finiteSpanningSetsInOpen

def MeasureTheory.Measure.finiteSpanningSetsInOpen' [TopologicalSpace α]
  [SecondCountableTopology α] {m : MeasurableSpace α} (μ : Measure α) [IsLocallyFiniteMeasure μ] :
  μ.FiniteSpanningSetsIn { K | IsOpen K } := by
  suffices H : Nonempty (μ.FiniteSpanningSetsIn { K | IsOpen K }) from H.some
  cases isEmpty_or_nonempty α
  · exact
      ⟨{  set := fun _ => ∅
          set_mem := fun _ => by simp
          finite := fun _ => by simp
          spanning := by simp [eq_iff_true_of_subsingleton] }⟩
  inhabit α
  let S : Set (Set α) := { s | IsOpen s ∧ μ s < ∞ }
  obtain ⟨T, T_count, TS, hT⟩ : ∃ T : Set (Set α), T.Countable ∧ T ⊆ S ∧ ⋃₀ T = ⋃₀ S :=
    isOpen_sUnion_countable S fun s hs => hs.1
  rw [μ.isTopologicalBasis_isOpen_lt_top.sUnion_eq] at hT
  have T_ne : T.Nonempty := by
    by_contra h'T
    rw [not_nonempty_iff_eq_empty.1 h'T, sUnion_empty] at hT
    simpa only [← hT] using mem_univ (default : α)
  obtain ⟨f, hf⟩ : ∃ f : ℕ → Set α, T = range f
  exact T_count.exists_eq_range T_ne
  have fS : ∀ n, f n ∈ S := by
    intro n
    apply TS
    rw [hf]
    exact mem_range_self n
  refine'
    ⟨{  set := f
        set_mem := fun n => (fS n).1
        finite := fun n => (fS n).2
        spanning := _ }⟩
  refine eq_univ_of_forall fun x => ?_
  obtain ⟨t, tT, xt⟩ : ∃ t : Set α, t ∈ range f ∧ x ∈ t := by
    have : x ∈ ⋃₀ T := by simp only [hT, mem_univ]
    simpa only [mem_sUnion, exists_prop, ← hf]
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, f n = t := by simpa only using tT
  exact mem_iUnion_of_mem _ xt
#align measure_theory.measure.finite_spanning_sets_in_open' MeasureTheory.Measure.finiteSpanningSetsInOpen'

structure is a type, which is useful if we want to record extra properties
  about the sets, such as that they are monotone.
  `SigmaFinite` is defined in terms of this: `μ` is σ-finite if there exists a sequence of
  finite spanning sets in the collection of all measurable sets. -/
-- Porting note(#5171): this linter isn't ported yet.

structure FiniteSpanningSetsIn {m0 : MeasurableSpace α} (μ : Measure α) (C : Set (Set α)) where
  protected set : ℕ → Set α
  protected set_mem : ∀ i, set i ∈ C
  protected finite : ∀ i, μ (set i) < ∞
  protected spanning : ⋃ i, set i = univ
#align measure_theory.measure.finite_spanning_sets_in MeasureTheory.Measure.FiniteSpanningSetsIn