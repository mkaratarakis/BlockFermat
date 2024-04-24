def IsSigmaCompact (s : Set X) : Prop :=
  ∃ K : ℕ → Set X, (∀ n, IsCompact (K n)) ∧ ⋃ n, K n = s

/-- Compact sets are σ-compact. -/
lemma IsCompact.isSigmaCompact {s : Set X} (hs : IsCompact s) : IsSigmaCompact s :=
  ⟨fun _ => s, fun _ => hs, iUnion_const _⟩

/-- The empty set is σ-compact. -/
@[simp]
lemma isSigmaCompact_empty : IsSigmaCompact (∅ : Set X) :=
  IsCompact.isSigmaCompact isCompact_empty

/-- Countable unions of compact sets are σ-compact. -/
lemma isSigmaCompact_iUnion_of_isCompact [hι : Countable ι] (s : ι → Set X)
    (hcomp : ∀ i, IsCompact (s i)) : IsSigmaCompact (⋃ i, s i) := by
  rcases isEmpty_or_nonempty ι
  · simp only [iUnion_of_empty, isSigmaCompact_empty]
  · -- If ι is non-empty, choose a surjection f : ℕ → ι, this yields a map ℕ → Set X.
    obtain ⟨f, hf⟩ := countable_iff_exists_surjective.mp hι
    exact ⟨s ∘ f, fun n ↦ hcomp (f n), Function.Surjective.iUnion_comp hf _⟩

/-- Countable unions of compact sets are σ-compact. -/
lemma isSigmaCompact_sUnion_of_isCompact {S : Set (Set X)} (hc : Set.Countable S)
    (hcomp : ∀ (s : Set X), s ∈ S → IsCompact s) : IsSigmaCompact (⋃₀ S) := by
  have : Countable S := countable_coe_iff.mpr hc
  rw [sUnion_eq_iUnion]
  apply isSigmaCompact_iUnion_of_isCompact _ (fun ⟨s, hs⟩ ↦ hcomp s hs)

/-- Countable unions of σ-compact sets are σ-compact. -/
lemma isSigmaCompact_iUnion [Countable ι] (s : ι → Set X)
    (hcomp : ∀ i, IsSigmaCompact (s i)) : IsSigmaCompact (⋃ i, s i) := by
  -- Choose a decomposition s_i = ⋃ K_i,j for each i.
  choose K hcomp hcov using fun i ↦ hcomp i
  -- Then, we have a countable union of countable unions of compact sets, i.e. countably many.
  have := calc
    ⋃ i, s i
    _ = ⋃ i, ⋃ n, (K i n) := by simp_rw [hcov]
    _ = ⋃ (i) (n : ℕ), (K.uncurry ⟨i, n⟩) := by rw [Function.uncurry_def]
    _ = ⋃ x, K.uncurry x := by rw [← iUnion_prod']
  rw [this]
  exact isSigmaCompact_iUnion_of_isCompact K.uncurry fun x ↦ (hcomp x.1 x.2)

/-- Countable unions of σ-compact sets are σ-compact. -/
lemma isSigmaCompact_sUnion (S : Set (Set X)) (hc : Set.Countable S)
    (hcomp : ∀ s : S, IsSigmaCompact s (X := X)) : IsSigmaCompact (⋃₀ S) := by
  have : Countable S := countable_coe_iff.mpr hc
  apply sUnion_eq_iUnion.symm ▸ isSigmaCompact_iUnion _ hcomp

/-- Countable unions of σ-compact sets are σ-compact. -/
lemma isSigmaCompact_biUnion {s : Set ι} {S : ι → Set X} (hc : Set.Countable s)
    (hcomp : ∀ (i : ι), i ∈ s → IsSigmaCompact (S i)) :
    IsSigmaCompact (⋃ (i : ι) (_ : i ∈ s), S i) := by
  have : Countable ↑s := countable_coe_iff.mpr hc
  rw [biUnion_eq_iUnion]
  exact isSigmaCompact_iUnion _ (fun ⟨i', hi'⟩ ↦ hcomp i' hi')

/-- A closed subset of a σ-compact set is σ-compact. -/
lemma IsSigmaCompact.of_isClosed_subset {s t : Set X} (ht : IsSigmaCompact t)
    (hs : IsClosed s) (h : s ⊆ t) : IsSigmaCompact s := by
  rcases ht with ⟨K, hcompact, hcov⟩
  refine ⟨(fun n ↦ s ∩ (K n)), fun n ↦ (hcompact n).inter_left hs, ?_⟩
  rw [← inter_iUnion, hcov]
  exact inter_eq_left.mpr h

/-- If `s` is σ-compact and `f` is continuous on `s`, `f(s)` is σ-compact. -/
lemma IsSigmaCompact.image_of_continuousOn {f : X → Y} {s : Set X} (hs : IsSigmaCompact s)
    (hf : ContinuousOn f s) : IsSigmaCompact (f '' s) := by
  rcases hs with ⟨K, hcompact, hcov⟩
  refine ⟨fun n ↦ f '' K n, ?_, hcov.symm ▸ image_iUnion.symm⟩
  exact fun n ↦ (hcompact n).image_of_continuousOn (hf.mono (hcov.symm ▸ subset_iUnion K n))

/-- If `s` is σ-compact and `f` continuous, `f(s)` is σ-compact. -/
lemma IsSigmaCompact.image {f : X → Y} (hf : Continuous f) {s : Set X} (hs : IsSigmaCompact s) :
    IsSigmaCompact (f '' s) := hs.image_of_continuousOn hf.continuousOn

/-- If `f : X → Y` is `Inducing`, the image `f '' s` of a set `s` is σ-compact
  if and only `s` is σ-compact. -/
lemma Inducing.isSigmaCompact_iff {f : X → Y} {s : Set X}
    (hf : Inducing f) : IsSigmaCompact s ↔ IsSigmaCompact (f '' s) := by
  constructor
  · exact fun h ↦ h.image hf.continuous
  · rintro ⟨L, hcomp, hcov⟩
    -- Suppose f(s) is σ-compact; we want to show s is σ-compact.
    -- Write f(s) as a union of compact sets L n, so s = ⋃ K n with K n := f⁻¹(L n) ∩ s.
    -- Since f is inducing, each K n is compact iff L n is.
    refine ⟨fun n ↦ f ⁻¹' (L n) ∩ s, ?_, ?_⟩
    · intro n
      have : f '' (f ⁻¹' (L n) ∩ s) = L n := by
        rw [image_preimage_inter, inter_eq_left.mpr]
        exact (subset_iUnion _ n).trans hcov.le
      apply hf.isCompact_iff.mpr (this.symm ▸ (hcomp n))
    · calc ⋃ n, f ⁻¹' L n ∩ s
        _ = f ⁻¹' (⋃ n, L n) ∩ s  := by rw [preimage_iUnion, iUnion_inter]
        _ = f ⁻¹' (f '' s) ∩ s := by rw [hcov]
        _ = s := inter_eq_right.mpr (subset_preimage_image _ _)

/-- If `f : X → Y` is an `Embedding`, the image `f '' s` of a set `s` is σ-compact
  if and only `s` is σ-compact. -/
lemma Embedding.isSigmaCompact_iff {f : X → Y} {s : Set X}
    (hf : Embedding f) : IsSigmaCompact s ↔ IsSigmaCompact (f '' s) :=
  hf.toInducing.isSigmaCompact_iff

/-- Sets of subtype are σ-compact iff the image under a coercion is. -/
lemma Subtype.isSigmaCompact_iff {p : X → Prop} {s : Set { a // p a }} :
    IsSigmaCompact s ↔ IsSigmaCompact ((↑) '' s : Set X) :=
  embedding_subtype_val.isSigmaCompact_iff

/-- A σ-compact space is a space that is the union of a countable collection of compact subspaces.
  Note that a locally compact separable T₂ space need not be σ-compact.
  The sequence can be extracted using `compactCovering`. -/
class SigmaCompactSpace (X : Type*) [TopologicalSpace X] : Prop where
  /-- In a σ-compact space, `Set.univ` is a σ-compact set. -/
  isSigmaCompact_univ : IsSigmaCompact (univ : Set X)
#align sigma_compact_space SigmaCompactSpace

def compactCovering : ℕ → Set X :=
  Accumulate exists_compact_covering.choose
#align compact_covering compactCovering

def LocallyFinite.encodable {ι : Type*} {f : ι → Set X}
    (hf : LocallyFinite f) (hne : ∀ i, (f i).Nonempty) : Encodable ι :=
  @Encodable.ofEquiv _ _ (hf.countable_univ hne).toEncodable (Equiv.Set.univ _).symm
#align locally_finite.encodable LocallyFinite.encodable

def find (x : X) : ℕ :=
  Nat.find (K.exists_mem x)
#align compact_exhaustion.find CompactExhaustion.find

def shiftr : CompactExhaustion X where
  toFun n := Nat.casesOn n ∅ K
  isCompact' n := Nat.casesOn n isCompact_empty K.isCompact
  subset_interior_succ' n := Nat.casesOn n (empty_subset _) K.subset_interior_succ
  iUnion_eq' := iUnion_eq_univ_iff.2 fun x => ⟨K.find x + 1, K.mem_find x⟩
#align compact_exhaustion.shiftr CompactExhaustion.shiftr

def choice (X : Type*) [TopologicalSpace X] [WeaklyLocallyCompactSpace X]
    [SigmaCompactSpace X] : CompactExhaustion X := by
  apply Classical.choice
  let K : ℕ → { s : Set X // IsCompact s } := fun n =>
    Nat.recOn n ⟨∅, isCompact_empty⟩ fun n s =>
      ⟨(exists_compact_superset s.2).choose ∪ compactCovering X n,
        (exists_compact_superset s.2).choose_spec.1.union (isCompact_compactCovering _ _)⟩
  refine' ⟨⟨fun n => (K n).1, fun n => (K n).2, fun n => _, _⟩⟩
  · exact Subset.trans (exists_compact_superset (K n).2).choose_spec.2
      (interior_mono <| subset_union_left _ _)
  · refine' univ_subset_iff.1 (iUnion_compactCovering X ▸ _)
    exact iUnion_mono' fun n => ⟨n + 1, subset_union_right _ _⟩
#align compact_exhaustion.choice CompactExhaustion.choice

structure CompactExhaustion (X : Type*) [TopologicalSpace X] where
  /-- The sequence of compact sets that form a compact exhaustion. -/
  toFun : ℕ → Set X
  /-- The sets in the compact exhaustion are in fact compact. -/
  isCompact' : ∀ n, IsCompact (toFun n)
  /-- The sets in the compact exhaustion form a sequence:
    each set is contained in the interior of the next. -/
  subset_interior_succ' : ∀ n, toFun n ⊆ interior (toFun (n + 1))
  /-- The union of all sets in a compact exhaustion equals the entire space. -/
  iUnion_eq' : ⋃ n, toFun n = univ
#align compact_exhaustion CompactExhaustion