def vectorSpan (s : Set P) : Submodule k V :=
  Submodule.span k (s -ᵥ s)
#align vector_span vectorSpan

def (s : Set P) : vectorSpan k s = Submodule.span k (s -ᵥ s) :=
  rfl
#align vector_span_def vectorSpan_def

def spanPoints (s : Set P) : Set P :=
  { p | ∃ p1 ∈ s, ∃ v ∈ vectorSpan k s, p = v +ᵥ p1 }
#align span_points spanPoints

def toAffineSubspace (p : Submodule k V) : AffineSubspace k V where
  carrier := p
  smul_vsub_vadd_mem _ _ _ _ h₁ h₂ h₃ := p.add_mem (p.smul_mem _ (p.sub_mem h₁ h₂)) h₃
#align submodule.to_affine_subspace Submodule.toAffineSubspace

def direction (s : AffineSubspace k P) : Submodule k V :=
  vectorSpan k (s : Set P)
#align affine_subspace.direction AffineSubspace.direction

def directionOfNonempty {s : AffineSubspace k P} (h : (s : Set P).Nonempty) : Submodule k V where
  carrier := (s : Set P) -ᵥ s
  zero_mem' := by
    cases' h with p hp
    exact vsub_self p ▸ vsub_mem_vsub hp hp
  add_mem' := by
    rintro _ _ ⟨p1, hp1, p2, hp2, rfl⟩ ⟨p3, hp3, p4, hp4, rfl⟩
    rw [← vadd_vsub_assoc]
    refine' vsub_mem_vsub _ hp4
    convert s.smul_vsub_vadd_mem 1 hp1 hp2 hp3
    rw [one_smul]
  smul_mem' := by
    rintro c _ ⟨p1, hp1, p2, hp2, rfl⟩
    rw [← vadd_vsub (c • (p1 -ᵥ p2)) p2]
    refine' vsub_mem_vsub _ hp2
    exact s.smul_vsub_vadd_mem c hp1 hp2 hp2
#align affine_subspace.direction_of_nonempty AffineSubspace.directionOfNonempty

def toAddTorsor (s : AffineSubspace k P) [Nonempty s] : AddTorsor s.direction s where
  vadd a b := ⟨(a : V) +ᵥ (b : P), vadd_mem_of_mem_direction a.2 b.2⟩
  zero_vadd := fun a => by
    ext
    exact zero_vadd _ _
  add_vadd a b c := by
    ext
    apply add_vadd
  vsub a b := ⟨(a : P) -ᵥ (b : P), (vsub_left_mem_direction_iff_mem a.2 _).mpr b.2⟩
  vsub_vadd' a b := by
    ext
    apply AddTorsor.vsub_vadd'
  vadd_vsub' a b := by
    ext
    apply AddTorsor.vadd_vsub'
#align affine_subspace.to_add_torsor AffineSubspace.toAddTorsor

def subtype (s : AffineSubspace k P) [Nonempty s] : s →ᵃ[k] P where
  toFun := (↑)
  linear := s.direction.subtype
  map_vadd' _ _ := rfl
#align affine_subspace.subtype AffineSubspace.subtype

def mk' (p : P) (direction : Submodule k V) : AffineSubspace k P where
  carrier := { q | ∃ v ∈ direction, q = v +ᵥ p }
  smul_vsub_vadd_mem c p1 p2 p3 hp1 hp2 hp3 := by
    rcases hp1 with ⟨v1, hv1, hp1⟩
    rcases hp2 with ⟨v2, hv2, hp2⟩
    rcases hp3 with ⟨v3, hv3, hp3⟩
    use c • (v1 - v2) + v3, direction.add_mem (direction.smul_mem c (direction.sub_mem hv1 hv2)) hv3
    simp [hp1, hp2, hp3, vadd_vadd]
#align affine_subspace.mk' AffineSubspace.mk'

def affineSpan (s : Set P) : AffineSubspace k P where
  carrier := spanPoints k s
  smul_vsub_vadd_mem c _ _ _ hp1 hp2 hp3 :=
    vadd_mem_spanPoints_of_mem_spanPoints_of_mem_vectorSpan k hp3
      ((vectorSpan k s).smul_mem c
        (vsub_mem_vectorSpan_of_mem_spanPoints_of_mem_spanPoints k hp1 hp2))
#align affine_span affineSpan

def (s1 s2 : AffineSubspace k P) : s1 ≤ s2 ↔ (s1 : Set P) ⊆ s2 :=
  Iff.rfl
#align affine_subspace.le_def AffineSubspace.le_def

def (s1 s2 : AffineSubspace k P) : s1 < s2 ↔ (s1 : Set P) ⊂ s2 :=
  Iff.rfl
#align affine_subspace.lt_def AffineSubspace.lt_def

def gi : GaloisInsertion (affineSpan k) ((↑) : AffineSubspace k P → Set P) where
  choice s _ := affineSpan k s
  gc s1 _s2 :=
    ⟨fun h => Set.Subset.trans (subset_spanPoints k s1) h, spanPoints_subset_coe_of_subset_coe⟩
  le_l_u _ := subset_spanPoints k _
  choice_eq _ _ := rfl
#align affine_subspace.gi AffineSubspace.gi

def topEquiv : (⊤ : AffineSubspace k P) ≃ᵃ[k] P where
  toEquiv := Equiv.Set.univ P
  linear := .ofEq _ _ (direction_top _ _ _) ≪≫ₗ Submodule.topEquiv
  map_vadd' _p _v := rfl

variable {P}

/-- No points are in `⊥`. -/
theorem not_mem_bot (p : P) : p ∉ (⊥ : AffineSubspace k P) :=
  Set.not_mem_empty p
#align affine_subspace.not_mem_bot AffineSubspace.not_mem_bot

def map (s : AffineSubspace k P₁) : AffineSubspace k P₂ where
  carrier := f '' s
  smul_vsub_vadd_mem := by
    rintro t - - - ⟨p₁, h₁, rfl⟩ ⟨p₂, h₂, rfl⟩ ⟨p₃, h₃, rfl⟩
    use t • (p₁ -ᵥ p₂) +ᵥ p₃
    suffices t • (p₁ -ᵥ p₂) +ᵥ p₃ ∈ s by
    { simp only [SetLike.mem_coe, true_and, this]
      rw [AffineMap.map_vadd, map_smul, AffineMap.linearMap_vsub] }
    exact s.smul_vsub_vadd_mem t h₁ h₂ h₃
#align affine_subspace.map AffineSubspace.map

def inclusion (h : S₁ ≤ S₂) : S₁ →ᵃ[k] S₂ where
  toFun := Set.inclusion h
  linear := Submodule.inclusion <| AffineSubspace.direction_le h
  map_vadd' _ _ := rfl

@[simp]
theorem coe_inclusion_apply (h : S₁ ≤ S₂) (x : S₁) : (inclusion h x : P₁) = x :=
  rfl

@[simp]
theorem inclusion_rfl : inclusion (le_refl S₁) = AffineMap.id k S₁ := rfl

end inclusion

end AffineSubspace

namespace AffineMap

@[simp]
theorem map_top_of_surjective (hf : Function.Surjective f) : AffineSubspace.map f ⊤ = ⊤ := by
  rw [← AffineSubspace.ext_iff]
  exact image_univ_of_surjective hf
#align affine_map.map_top_of_surjective AffineMap.map_top_of_surjective

def ofEq (h : S₁ = S₂) : S₁ ≃ᵃ[k] S₂ where
  toEquiv := Equiv.Set.ofEq <| congr_arg _ h
  linear := .ofEq _ _ <| congr_arg _ h
  map_vadd' _ _ := rfl

@[simp]
theorem coe_ofEq_apply (h : S₁ = S₂) (x : S₁) : (ofEq S₁ S₂ h x : P₁) = x :=
  rfl

@[simp]
theorem ofEq_symm (h : S₁ = S₂) : (ofEq S₁ S₂ h).symm = ofEq S₂ S₁ h.symm :=
  rfl

@[simp]
theorem ofEq_rfl : ofEq S₁ S₁ rfl = AffineEquiv.refl k S₁ := rfl

end ofEq

theorem span_eq_top_iff {s : Set P₁} (e : P₁ ≃ᵃ[k] P₂) :
    affineSpan k s = ⊤ ↔ affineSpan k (e '' s) = ⊤ := by
  refine' ⟨(e : P₁ →ᵃ[k] P₂).span_eq_top_of_surjective e.surjective, _⟩
  intro h
  have : s = e.symm '' (e '' s) := by rw [← image_comp]; simp
  rw [this]
  exact (e.symm : P₂ →ᵃ[k] P₁).span_eq_top_of_surjective e.symm.surjective h
#align affine_equiv.span_eq_top_iff AffineEquiv.span_eq_top_iff

def comap (f : P₁ →ᵃ[k] P₂) (s : AffineSubspace k P₂) : AffineSubspace k P₁ where
  carrier := f ⁻¹' s
  smul_vsub_vadd_mem t p₁ p₂ p₃ (hp₁ : f p₁ ∈ s) (hp₂ : f p₂ ∈ s) (hp₃ : f p₃ ∈ s) :=
    show f _ ∈ s by
      rw [AffineMap.map_vadd, LinearMap.map_smul, AffineMap.linearMap_vsub]
      apply s.smul_vsub_vadd_mem _ hp₁ hp₂ hp₃
#align affine_subspace.comap AffineSubspace.comap

def Parallel (s₁ s₂ : AffineSubspace k P) : Prop :=
  ∃ v : V, s₂ = s₁.map (constVAdd k P v)
#align affine_subspace.parallel AffineSubspace.Parallel

structure on affine subspaces.
* `AffineSubspace.direction` gives the `Submodule` spanned by the pairwise differences of points
  in an `AffineSubspace`. There are various lemmas relating to the set of vectors in the
  `direction`, and relating the lattice structure on affine subspaces to that on their directions.
* `AffineSubspace.parallel`, notation `∥`, gives the property of two affine subspaces being
  parallel (one being a translate of the other).
* `affineSpan` gives the affine subspace spanned by a set of points, with `vectorSpan` giving its
  direction. The `affineSpan` is defined in terms of `spanPoints`, which gives an explicit
  description of the points contained in the affine span; `spanPoints` itself should generally only
  be used when that description is required, with `affineSpan` being the main definition for other
  purposes. Two other descriptions of the affine span are proved equivalent: it is the `sInf` of
  affine subspaces containing the points, and (if `[Nontrivial k]`) it contains exactly those points
  that are affine combinations of points in the given set.

## Implementation notes

structure induced by a corresponding subspace of the `Module k V`. -/
structure AffineSubspace (k : Type*) {V : Type*} (P : Type*) [Ring k] [AddCommGroup V]
  [Module k V] [AffineSpace V P] where
  /-- The affine subspace seen as a subset. -/
  carrier : Set P
  smul_vsub_vadd_mem :
    ∀ (c : k) {p1 p2 p3 : P},
      p1 ∈ carrier → p2 ∈ carrier → p3 ∈ carrier → c • (p1 -ᵥ p2 : V) +ᵥ p3 ∈ carrier
#align affine_subspace AffineSubspace