def restrict (f : ι →ᵇᵃ[I₀] M) (I : WithTop (Box ι)) (hI : I ≤ I₀) : ι →ᵇᵃ[I] M :=
  ⟨f, fun J hJ => f.2 J (hJ.trans hI)⟩
#align box_integral.box_additive_map.restrict BoxIntegral.BoxAdditiveMap.restrict

def ofMapSplitAdd [Finite ι] (f : Box ι → M) (I₀ : WithTop (Box ι))
    (hf : ∀ I : Box ι, ↑I ≤ I₀ → ∀ {i x}, x ∈ Ioo (I.lower i) (I.upper i) →
      (I.splitLower i x).elim' 0 f + (I.splitUpper i x).elim' 0 f = f I) :
    ι →ᵇᵃ[I₀] M := by
  refine' ⟨f, _⟩
  replace hf : ∀ I : Box ι, ↑I ≤ I₀ → ∀ s, (∑ J in (splitMany I s).boxes, f J) = f I := by
    intro I hI s
    induction' s using Finset.induction_on with a s _ ihs
    · simp
    rw [splitMany_insert, inf_split, ← ihs, biUnion_boxes, sum_biUnion_boxes]
    refine' Finset.sum_congr rfl fun J' hJ' => _
    by_cases h : a.2 ∈ Ioo (J'.lower a.1) (J'.upper a.1)
    · rw [sum_split_boxes]
      exact hf _ ((WithTop.coe_le_coe.2 <| le_of_mem _ hJ').trans hI) h
    · rw [split_of_not_mem_Ioo h, top_boxes, Finset.sum_singleton]
  intro I hI π hπ
  have Hle : ∀ J ∈ π, ↑J ≤ I₀ := fun J hJ => (WithTop.coe_le_coe.2 <| π.le_of_mem hJ).trans hI
  rcases hπ.exists_splitMany_le with ⟨s, hs⟩
  rw [← hf _ hI, ← inf_of_le_right hs, inf_splitMany, biUnion_boxes, sum_biUnion_boxes]
  exact Finset.sum_congr rfl fun J hJ => (hf _ (Hle _ hJ) _).symm
#align box_integral.box_additive_map.of_map_split_add BoxIntegral.BoxAdditiveMap.ofMapSplitAdd

def map (f : ι →ᵇᵃ[I₀] M) (g : M →+ N) : ι →ᵇᵃ[I₀] N where
  toFun := g ∘ f
  sum_partition_boxes' I hI π hπ := by simp_rw [comp, ← map_sum, f.sum_partition_boxes hI hπ]
#align box_integral.box_additive_map.map BoxIntegral.BoxAdditiveMap.map

def toSMul (f : ι →ᵇᵃ[I₀] ℝ) : ι →ᵇᵃ[I₀] E →L[ℝ] E :=
  f.map (ContinuousLinearMap.lsmul ℝ ℝ).toLinearMap.toAddMonoidHom
#align box_integral.box_additive_map.to_smul BoxIntegral.BoxAdditiveMap.toSMul

def upperSubLower.{u} {G : Type u} [AddCommGroup G] (I₀ : Box (Fin (n + 1))) (i : Fin (n + 1))
    (f : ℝ → Box (Fin n) → G) (fb : Icc (I₀.lower i) (I₀.upper i) → Fin n →ᵇᵃ[I₀.face i] G)
    (hf : ∀ (x) (hx : x ∈ Icc (I₀.lower i) (I₀.upper i)) (J), f x J = fb ⟨x, hx⟩ J) :
    Fin (n + 1) →ᵇᵃ[I₀] G :=
  ofMapSplitAdd (fun J : Box (Fin (n + 1)) => f (J.upper i) (J.face i) - f (J.lower i) (J.face i))
    I₀
    (by
      intro J hJ j x
      rw [WithTop.coe_le_coe] at hJ
      refine' i.succAboveCases (fun hx => _) (fun j hx => _) j
      · simp only [Box.splitLower_def hx, Box.splitUpper_def hx, update_same, ← WithBot.some_eq_coe,
          Option.elim', Box.face, (· ∘ ·), update_noteq (Fin.succAbove_ne _ _)]
        abel
      · have : (J.face i : WithTop (Box (Fin n))) ≤ I₀.face i :=
          WithTop.coe_le_coe.2 (face_mono hJ i)
        rw [le_iff_Icc, @Box.Icc_eq_pi _ I₀] at hJ
        simp only
        rw [hf _ (hJ J.upper_mem_Icc _ trivial), hf _ (hJ J.lower_mem_Icc _ trivial),
          ← (fb _).map_split_add this j x, ← (fb _).map_split_add this j x]
        have hx' : x ∈ Ioo ((J.face i).lower j) ((J.face i).upper j) := hx
        simp only [Box.splitLower_def hx, Box.splitUpper_def hx, Box.splitLower_def hx',
          Box.splitUpper_def hx', ← WithBot.some_eq_coe, Option.elim', Box.face_mk,
          update_noteq (Fin.succAbove_ne _ _).symm, sub_add_sub_comm,
          update_comp_eq_of_injective _ (Fin.strictMono_succAbove i).injective j x, ← hf]
        simp only [Box.face])
#align box_integral.box_additive_map.upper_sub_lower BoxIntegral.BoxAdditiveMap.upperSubLower

structure BoxAdditiveMap (ι M : Type*) [AddCommMonoid M] (I : WithTop (Box ι)) where
  toFun : Box ι → M
  sum_partition_boxes' : ∀ J : Box ι, ↑J ≤ I → ∀ π : Prepartition J, π.IsPartition →
    ∑ Ji in π.boxes, toFun Ji = toFun J
#align box_integral.box_additive_map BoxIntegral.BoxAdditiveMap