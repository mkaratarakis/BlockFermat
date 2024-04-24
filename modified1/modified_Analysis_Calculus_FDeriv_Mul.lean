def (f · x) (l.get ·), ← List.map_map, List.map_take, List.map_drop]

/--
Unlike `HasFDerivAt.finset_prod`, supports non-commutative multiply and duplicate elements.
-/
@[fun_prop]
theorem HasFDerivAt.list_prod' {l : List ι} {x : E}
    (h : ∀ i ∈ l, HasFDerivAt (f i ·) (f' i) x) :
    HasFDerivAt (fun x ↦ (l.map (f · x)).prod)
      (∑ i : Fin l.length, ((l.take i).map (f · x)).prod •
        smulRight (f' (l.get i)) ((l.drop (.succ i)).map (f · x)).prod) x := by
  simp only [← List.finRange_map_get l, List.map_map]
  refine .congr_fderiv (hasFDerivAt_list_prod_finRange'.comp x
    (hasFDerivAt_pi.mpr fun i ↦ h (l.get i) (l.get_mem i i.isLt))) ?_
  ext m
  simp [← Function.comp_def (f · x) (l.get ·), ← List.map_map, List.map_take, List.map_drop]

@[fun_prop]
theorem HasFDerivWithinAt.list_prod' {l : List ι} {x : E}
    (h : ∀ i ∈ l, HasFDerivWithinAt (f i ·) (f' i) s x) :
    HasFDerivWithinAt (fun x ↦ (l.map (f · x)).prod)
      (∑ i : Fin l.length, ((l.take i).map (f · x)).prod •
        smulRight (f' (l.get i)) ((l.drop (.succ i)).map (f · x)).prod) s x := by
  simp only [← List.finRange_map_get l, List.map_map]
  refine .congr_fderiv (hasFDerivAt_list_prod_finRange'.comp_hasFDerivWithinAt x
    (hasFDerivWithinAt_pi.mpr fun i ↦ h (l.get i) (l.get_mem i i.isLt))) ?_
  ext m
  simp [← Function.comp_def (f · x) (l.get ·), ← List.map_map, List.map_take, List.map_drop]

theorem fderiv_list_prod' {l : List ι} {x : E}
    (h : ∀ i ∈ l, DifferentiableAt 𝕜 (f i ·) x) :
    fderiv 𝕜 (fun x ↦ (l.map (f · x)).prod) x =
      ∑ i : Fin l.length, ((l.take i).map (f · x)).prod •
        smulRight (fderiv 𝕜 (fun x ↦ f (l.get i) x) x)
          ((l.drop (.succ i)).map (f · x)).prod :=
  (HasFDerivAt.list_prod' fun i hi ↦ (h i hi).hasFDerivAt).fderiv

theorem fderivWithin_list_prod' {l : List ι} {x : E}
    (hxs : UniqueDiffWithinAt 𝕜 s x) (h : ∀ i ∈ l, DifferentiableWithinAt 𝕜 (f i ·) s x) :
    fderivWithin 𝕜 (fun x ↦ (l.map (f · x)).prod) s x =
      ∑ i : Fin l.length, ((l.take i).map (f · x)).prod •
        smulRight (fderivWithin 𝕜 (fun x ↦ f (l.get i) x) s x)
          ((l.drop (.succ i)).map (f · x)).prod :=
  (HasFDerivWithinAt.list_prod' fun i hi ↦ (h i hi).hasFDerivWithinAt).fderivWithin hxs

@[fun_prop]
theorem HasStrictFDerivAt.multiset_prod [DecidableEq ι] {u : Multiset ι} {x : E}
    (h : ∀ i ∈ u, HasStrictFDerivAt (g i ·) (g' i) x) :
    HasStrictFDerivAt (fun x ↦ (u.map (g · x)).prod)
      (u.map fun i ↦ ((u.erase i).map (g · x)).prod • g' i).sum x := by
  simp only [← Multiset.attach_map_val u, Multiset.map_map]
  exact .congr_fderiv
    (hasStrictFDerivAt_multiset_prod.comp x <| hasStrictFDerivAt_pi.mpr fun i ↦ h i i.prop)
    (by ext; simp [Finset.sum_multiset_map_count, u.erase_attach_map (g · x)])

/--
Unlike `HasFDerivAt.finset_prod`, supports duplicate elements.
-/
@[fun_prop]
theorem HasFDerivAt.multiset_prod [DecidableEq ι] {u : Multiset ι} {x : E}
    (h : ∀ i ∈ u, HasFDerivAt (g i ·) (g' i) x) :
    HasFDerivAt (fun x ↦ (u.map (g · x)).prod)
      (u.map fun i ↦ ((u.erase i).map (g · x)).prod • g' i).sum x := by
  simp only [← Multiset.attach_map_val u, Multiset.map_map]
  exact .congr_fderiv
    (hasFDerivAt_multiset_prod.comp x <| hasFDerivAt_pi.mpr fun i ↦ h i i.prop)
    (by ext; simp [Finset.sum_multiset_map_count, u.erase_attach_map (g · x)])

@[fun_prop]
theorem HasFDerivWithinAt.multiset_prod [DecidableEq ι] {u : Multiset ι} {x : E}
    (h : ∀ i ∈ u, HasFDerivWithinAt (g i ·) (g' i) s x) :
    HasFDerivWithinAt (fun x ↦ (u.map (g · x)).prod)
      (u.map fun i ↦ ((u.erase i).map (g · x)).prod • g' i).sum s x := by
  simp only [← Multiset.attach_map_val u, Multiset.map_map]
  exact .congr_fderiv
    (hasFDerivAt_multiset_prod.comp_hasFDerivWithinAt x <|
      hasFDerivWithinAt_pi.mpr fun i ↦ h i i.prop)
    (by ext; simp [Finset.sum_multiset_map_count, u.erase_attach_map (g · x)])

theorem fderiv_multiset_prod [DecidableEq ι] {u : Multiset ι} {x : E}
    (h : ∀ i ∈ u, DifferentiableAt 𝕜 (g i ·) x) :
    fderiv 𝕜 (fun x ↦ (u.map (g · x)).prod) x =
      (u.map fun i ↦ ((u.erase i).map (g · x)).prod • fderiv 𝕜 (g i) x).sum :=
  (HasFDerivAt.multiset_prod fun i hi ↦ (h i hi).hasFDerivAt).fderiv

theorem fderivWithin_multiset_prod [DecidableEq ι] {u : Multiset ι} {x : E}
    (hxs : UniqueDiffWithinAt 𝕜 s x) (h : ∀ i ∈ u, DifferentiableWithinAt 𝕜 (g i ·) s x) :
    fderivWithin 𝕜 (fun x ↦ (u.map (g · x)).prod) s x =
      (u.map fun i ↦ ((u.erase i).map (g · x)).prod • fderivWithin 𝕜 (g i) s x).sum :=
  (HasFDerivWithinAt.multiset_prod fun i hi ↦ (h i hi).hasFDerivWithinAt).fderivWithin hxs

theorem HasStrictFDerivAt.finset_prod [DecidableEq ι] {x : E}
    (hg : ∀ i ∈ u, HasStrictFDerivAt (g i) (g' i) x) :
    HasStrictFDerivAt (∏ i in u, g i ·) (∑ i in u, (∏ j in u.erase i, g j x) • g' i) x := by
  simpa [← Finset.prod_attach u] using .congr_fderiv
    (hasStrictFDerivAt_finset_prod.comp x <| hasStrictFDerivAt_pi.mpr fun i ↦ hg i i.prop)
    (by ext; simp [Finset.prod_erase_attach (g · x), ← u.sum_attach])

theorem HasFDerivAt.finset_prod [DecidableEq ι] {x : E}
    (hg : ∀ i ∈ u, HasFDerivAt (g i) (g' i) x) :
    HasFDerivAt (∏ i in u, g i ·) (∑ i in u, (∏ j in u.erase i, g j x) • g' i) x := by
  simpa [← Finset.prod_attach u] using .congr_fderiv
    (hasFDerivAt_finset_prod.comp x <| hasFDerivAt_pi.mpr fun i ↦ hg i i.prop)
    (by ext; simp [Finset.prod_erase_attach (g · x), ← u.sum_attach])

theorem HasFDerivWithinAt.finset_prod [DecidableEq ι] {x : E}
    (hg : ∀ i ∈ u, HasFDerivWithinAt (g i) (g' i) s x) :
    HasFDerivWithinAt (∏ i in u, g i ·) (∑ i in u, (∏ j in u.erase i, g j x) • g' i) s x := by
  simpa [← Finset.prod_attach u] using .congr_fderiv
    (hasFDerivAt_finset_prod.comp_hasFDerivWithinAt x <|
      hasFDerivWithinAt_pi.mpr fun i ↦ hg i i.prop)
    (by ext; simp [Finset.prod_erase_attach (g · x), ← u.sum_attach])

theorem fderiv_finset_prod [DecidableEq ι] {x : E} (hg : ∀ i ∈ u, DifferentiableAt 𝕜 (g i) x) :
    fderiv 𝕜 (∏ i in u, g i ·) x = ∑ i in u, (∏ j in u.erase i, (g j x)) • fderiv 𝕜 (g i) x :=
  (HasFDerivAt.finset_prod fun i hi ↦ (hg i hi).hasFDerivAt).fderiv

theorem fderivWithin_finset_prod [DecidableEq ι] {x : E} (hxs : UniqueDiffWithinAt 𝕜 s x)
    (hg : ∀ i ∈ u, DifferentiableWithinAt 𝕜 (g i) s x) :
    fderivWithin 𝕜 (∏ i in u, g i ·) s x =
      ∑ i in u, (∏ j in u.erase i, (g j x)) • fderivWithin 𝕜 (g i) s x :=
  (HasFDerivWithinAt.finset_prod fun i hi ↦ (hg i hi).hasFDerivWithinAt).fderivWithin hxs

end Comp

end Prod

section AlgebraInverse

variable {R : Type*} [NormedRing R] [NormedAlgebra 𝕜 R] [CompleteSpace R]

open NormedRing ContinuousLinearMap Ring

/-- At an invertible element `x` of a normed algebra `R`, the Fréchet derivative of the inversion
operation is the linear map `fun t ↦ - x⁻¹ * t * x⁻¹`.

TODO: prove that `Ring.inverse` is analytic and use it to prove a `HasStrictFDerivAt` lemma.
TODO (low prio): prove a version without assumption `[CompleteSpace R]` but within the set of
units. -/
@[fun_prop]
theorem hasFDerivAt_ring_inverse (x : Rˣ) :
    HasFDerivAt Ring.inverse (-mulLeftRight 𝕜 R ↑x⁻¹ ↑x⁻¹) x :=
  have : (fun t : R => Ring.inverse (↑x + t) - ↑x⁻¹ + ↑x⁻¹ * t * ↑x⁻¹) =o[𝓝 0] id :=
    (inverse_add_norm_diff_second_order x).trans_isLittleO (isLittleO_norm_pow_id one_lt_two)
  by simpa [hasFDerivAt_iff_isLittleO_nhds_zero] using this
#align has_fderiv_at_ring_inverse hasFDerivAt_ring_inverse