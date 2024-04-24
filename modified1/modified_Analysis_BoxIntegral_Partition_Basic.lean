def single (I J : Box ι) (h : J ≤ I) : Prepartition I :=
  ⟨{J}, by simpa, by simp⟩
#align box_integral.prepartition.single BoxIntegral.Prepartition.single

def : π₁ ≤ π₂ ↔ ∀ J ∈ π₁, ∃ J' ∈ π₂, J ≤ J' := Iff.rfl
#align box_integral.prepartition.le_def BoxIntegral.Prepartition.le_def

def iUnion : Set (ι → ℝ) :=
  ⋃ J ∈ π, ↑J
#align box_integral.prepartition.Union BoxIntegral.Prepartition.iUnion

def : π.iUnion = ⋃ J ∈ π, ↑J := rfl
#align box_integral.prepartition.Union_def BoxIntegral.Prepartition.iUnion_def

def biUnion (πi : ∀ J : Box ι, Prepartition J) : Prepartition I where
  boxes := π.boxes.biUnion fun J => (πi J).boxes
  le_of_mem' J hJ := by
    simp only [Finset.mem_biUnion, exists_prop, mem_boxes] at hJ
    rcases hJ with ⟨J', hJ', hJ⟩
    exact ((πi J').le_of_mem hJ).trans (π.le_of_mem hJ')
  pairwiseDisjoint := by
    simp only [Set.Pairwise, Finset.mem_coe, Finset.mem_biUnion]
    rintro J₁' ⟨J₁, hJ₁, hJ₁'⟩ J₂' ⟨J₂, hJ₂, hJ₂'⟩ Hne
    rw [Function.onFun, Set.disjoint_left]
    rintro x hx₁ hx₂; apply Hne
    obtain rfl : J₁ = J₂
    exact π.eq_of_mem_of_mem hJ₁ hJ₂ ((πi J₁).le_of_mem hJ₁' hx₁) ((πi J₂).le_of_mem hJ₂' hx₂)
    exact (πi J₁).eq_of_mem_of_mem hJ₁' hJ₂' hx₁ hx₂
#align box_integral.prepartition.bUnion BoxIntegral.Prepartition.biUnion

def biUnionIndex (πi : ∀ (J : Box ι), Prepartition J) (J : Box ι) : Box ι :=
  if hJ : J ∈ π.biUnion πi then (π.mem_biUnion.1 hJ).choose else I
#align box_integral.prepartition.bUnion_index BoxIntegral.Prepartition.biUnionIndex

def ofWithBot (boxes : Finset (WithBot (Box ι)))
    (le_of_mem : ∀ J ∈ boxes, (J : WithBot (Box ι)) ≤ I)
    (pairwise_disjoint : Set.Pairwise (boxes : Set (WithBot (Box ι))) Disjoint) :
    Prepartition I where
  boxes := Finset.eraseNone boxes
  le_of_mem' J hJ := by
    rw [mem_eraseNone] at hJ
    simpa only [WithBot.some_eq_coe, WithBot.coe_le_coe] using le_of_mem _ hJ
  pairwiseDisjoint J₁ h₁ J₂ h₂ hne := by
    simp only [mem_coe, mem_eraseNone] at h₁ h₂
    exact Box.disjoint_coe.1 (pairwise_disjoint h₁ h₂ (mt Option.some_inj.1 hne))
#align box_integral.prepartition.of_with_bot BoxIntegral.Prepartition.ofWithBot

def restrict (π : Prepartition I) (J : Box ι) : Prepartition J :=
  ofWithBot (π.boxes.image fun J' : Box ι => J ⊓ J')
    (fun J' hJ' => by
      rcases Finset.mem_image.1 hJ' with ⟨J', -, rfl⟩
      exact inf_le_left)
    (by
      simp only [Set.Pairwise, onFun, Finset.mem_coe, Finset.mem_image]
      rintro _ ⟨J₁, h₁, rfl⟩ _ ⟨J₂, h₂, rfl⟩ Hne
      have : J₁ ≠ J₂ := by
        rintro rfl
        exact Hne rfl
      exact ((Box.disjoint_coe.2 <| π.disjoint_coe_of_mem h₁ h₂ this).inf_left' _).inf_right' _)
#align box_integral.prepartition.restrict BoxIntegral.Prepartition.restrict

def (π₁ π₂ : Prepartition I) : π₁ ⊓ π₂ = π₁.biUnion fun J => π₂.restrict J := rfl
#align box_integral.prepartition.inf_def BoxIntegral.Prepartition.inf_def

def filter (π : Prepartition I) (p : Box ι → Prop) : Prepartition I where
  boxes := π.boxes.filter p
  le_of_mem' _ hJ := π.le_of_mem (mem_filter.1 hJ).1
  pairwiseDisjoint _ h₁ _ h₂ := π.disjoint_coe_of_mem (mem_filter.1 h₁).1 (mem_filter.1 h₂).1
#align box_integral.prepartition.filter BoxIntegral.Prepartition.filter

def disjUnion (π₁ π₂ : Prepartition I) (h : Disjoint π₁.iUnion π₂.iUnion) : Prepartition I where
  boxes := π₁.boxes ∪ π₂.boxes
  le_of_mem' J hJ := (Finset.mem_union.1 hJ).elim π₁.le_of_mem π₂.le_of_mem
  pairwiseDisjoint :=
    suffices ∀ J₁ ∈ π₁, ∀ J₂ ∈ π₂, J₁ ≠ J₂ → Disjoint (J₁ : Set (ι → ℝ)) J₂ by
      simpa [pairwise_union_of_symmetric (symmetric_disjoint.comap _), pairwiseDisjoint]
    fun J₁ h₁ J₂ h₂ _ => h.mono (π₁.subset_iUnion h₁) (π₂.subset_iUnion h₂)
#align box_integral.prepartition.disj_union BoxIntegral.Prepartition.disjUnion

def distortion : ℝ≥0 :=
  π.boxes.sup Box.distortion
#align box_integral.prepartition.distortion BoxIntegral.Prepartition.distortion

def IsPartition (π : Prepartition I) :=
  ∀ x ∈ I, ∃ J ∈ π, x ∈ J
#align box_integral.prepartition.is_partition BoxIntegral.Prepartition.IsPartition

structure `BoxIntegral.Prepartition (I : BoxIntegral.Box ι)` that stores a collection of boxes
such that

* each box `J ∈ boxes` is a subbox of `I`;
* the boxes are pairwise disjoint as sets in `ℝⁿ`.

Then we define a predicate `BoxIntegral.Prepartition.IsPartition`; `π.IsPartition` means that the
boxes of `π` actually cover the whole `I`. We also define some operations on prepartitions:

* `BoxIntegral.Prepartition.biUnion`: split each box of a partition into smaller boxes;
* `BoxIntegral.Prepartition.restrict`: restrict a partition to a smaller box.

We also define a `SemilatticeInf` structure on `BoxIntegral.Prepartition I` for all
`I : BoxIntegral.Box ι`.

## Tags

structure Prepartition (I : Box ι) where
  boxes : Finset (Box ι)
  le_of_mem' : ∀ J ∈ boxes, J ≤ I
  pairwiseDisjoint : Set.Pairwise (↑boxes) (Disjoint on ((↑) : Box ι → Set (ι → ℝ)))
#align box_integral.prepartition BoxIntegral.Prepartition