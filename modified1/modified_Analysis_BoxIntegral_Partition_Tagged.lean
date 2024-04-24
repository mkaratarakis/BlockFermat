def iUnion : Set (ι → ℝ) :=
  π.toPrepartition.iUnion
#align box_integral.tagged_prepartition.Union BoxIntegral.TaggedPrepartition.iUnion

def : π.iUnion = ⋃ J ∈ π, ↑J := rfl
#align box_integral.tagged_prepartition.Union_def BoxIntegral.TaggedPrepartition.iUnion_def

def IsPartition :=
  π.toPrepartition.IsPartition
#align box_integral.tagged_prepartition.is_partition BoxIntegral.TaggedPrepartition.IsPartition

def filter (p : Box ι → Prop) : TaggedPrepartition I :=
  ⟨π.1.filter p, π.2, π.3⟩
#align box_integral.tagged_prepartition.filter BoxIntegral.TaggedPrepartition.filter

def biUnionTagged (π : Prepartition I) (πi : ∀ J : Box ι, TaggedPrepartition J) :
    TaggedPrepartition I where
  toPrepartition := π.biUnion fun J => (πi J).toPrepartition
  tag J := (πi (π.biUnionIndex (fun J => (πi J).toPrepartition) J)).tag J
  tag_mem_Icc _ := Box.le_iff_Icc.1 (π.biUnionIndex_le _ _) ((πi _).tag_mem_Icc _)
#align box_integral.prepartition.bUnion_tagged BoxIntegral.Prepartition.biUnionTagged

def biUnionPrepartition (π : TaggedPrepartition I) (πi : ∀ J : Box ι, Prepartition J) :
    TaggedPrepartition I where
  toPrepartition := π.toPrepartition.biUnion πi
  tag J := π.tag (π.toPrepartition.biUnionIndex πi J)
  tag_mem_Icc _ := π.tag_mem_Icc _
#align box_integral.tagged_prepartition.bUnion_prepartition BoxIntegral.TaggedPrepartition.biUnionPrepartition

def infPrepartition (π : TaggedPrepartition I) (π' : Prepartition I) : TaggedPrepartition I :=
  π.biUnionPrepartition fun J => π'.restrict J
#align box_integral.tagged_prepartition.inf_prepartition BoxIntegral.TaggedPrepartition.infPrepartition

def IsHenstock (π : TaggedPrepartition I) : Prop :=
  ∀ J ∈ π, π.tag J ∈ Box.Icc J
set_option linter.uppercaseLean3 false in
#align box_integral.tagged_prepartition.is_Henstock BoxIntegral.TaggedPrepartition.IsHenstock

def IsSubordinate [Fintype ι] (π : TaggedPrepartition I) (r : (ι → ℝ) → Ioi (0 : ℝ)) : Prop :=
  ∀ J ∈ π, Box.Icc J ⊆ closedBall (π.tag J) (r <| π.tag J)
#align box_integral.tagged_prepartition.is_subordinate BoxIntegral.TaggedPrepartition.IsSubordinate

def single (I J : Box ι) (hJ : J ≤ I) (x : ι → ℝ) (h : x ∈ Box.Icc I) : TaggedPrepartition I :=
  ⟨Prepartition.single I J hJ, fun _ => x, fun _ => h⟩
#align box_integral.tagged_prepartition.single BoxIntegral.TaggedPrepartition.single

def disjUnion (π₁ π₂ : TaggedPrepartition I) (h : Disjoint π₁.iUnion π₂.iUnion) :
    TaggedPrepartition I where
  toPrepartition := π₁.toPrepartition.disjUnion π₂.toPrepartition h
  tag := π₁.boxes.piecewise π₁.tag π₂.tag
  tag_mem_Icc J := by
    dsimp only [Finset.piecewise]
    split_ifs
    exacts [π₁.tag_mem_Icc J, π₂.tag_mem_Icc J]
#align box_integral.tagged_prepartition.disj_union BoxIntegral.TaggedPrepartition.disjUnion

def embedBox (I J : Box ι) (h : I ≤ J) : TaggedPrepartition I ↪ TaggedPrepartition J where
  toFun π :=
    { π with
      le_of_mem' := fun J' hJ' => (π.le_of_mem' J' hJ').trans h
      tag_mem_Icc := fun J => Box.le_iff_Icc.1 h (π.tag_mem_Icc J) }
  inj' := by
    rintro ⟨⟨b₁, h₁le, h₁d⟩, t₁, ht₁⟩ ⟨⟨b₂, h₂le, h₂d⟩, t₂, ht₂⟩ H
    simpa using H
#align box_integral.tagged_prepartition.embed_box BoxIntegral.TaggedPrepartition.embedBox

def distortion : ℝ≥0 :=
  π.toPrepartition.distortion
#align box_integral.tagged_prepartition.distortion BoxIntegral.TaggedPrepartition.distortion

structure TaggedPrepartition (I : Box ι) extends Prepartition I where
  tag : Box ι → ι → ℝ
  tag_mem_Icc : ∀ J, tag J ∈ Box.Icc I
#align box_integral.tagged_prepartition BoxIntegral.TaggedPrepartition