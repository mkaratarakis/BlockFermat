def partialHomeomorph (φ : B → F ≃L[𝕜] F) (hU : IsOpen U)
    (hφ : ContinuousOn (fun x => φ x : B → F →L[𝕜] F) U)
    (h2φ : ContinuousOn (fun x => (φ x).symm : B → F →L[𝕜] F) U) :
    PartialHomeomorph (B × F) (B × F) where
  toFun x := (x.1, φ x.1 x.2)
  invFun x := (x.1, (φ x.1).symm x.2)
  source := U ×ˢ univ
  target := U ×ˢ univ
  map_source' _x hx := mk_mem_prod hx.1 (mem_univ _)
  map_target' _x hx := mk_mem_prod hx.1 (mem_univ _)
  left_inv' _ _ := Prod.ext rfl (ContinuousLinearEquiv.symm_apply_apply _ _)
  right_inv' _ _ := Prod.ext rfl (ContinuousLinearEquiv.apply_symm_apply _ _)
  open_source := hU.prod isOpen_univ
  open_target := hU.prod isOpen_univ
  continuousOn_toFun :=
    have : ContinuousOn (fun p : B × F => ((φ p.1 : F →L[𝕜] F), p.2)) (U ×ˢ univ) :=
      hφ.prod_map continuousOn_id
    continuousOn_fst.prod (isBoundedBilinearMap_apply.continuous.comp_continuousOn this)
  continuousOn_invFun :=
    haveI : ContinuousOn (fun p : B × F => (((φ p.1).symm : F →L[𝕜] F), p.2)) (U ×ˢ univ) :=
      h2φ.prod_map continuousOn_id
    continuousOn_fst.prod (isBoundedBilinearMap_apply.continuous.comp_continuousOn this)
#align fiberwise_linear.local_homeomorph FiberwiseLinear.partialHomeomorph

def smoothFiberwiseLinear : StructureGroupoid (B × F) where
  members :=
    ⋃ (φ : B → F ≃L[𝕜] F) (U : Set B) (hU : IsOpen U)
      (hφ : SmoothOn IB 𝓘(𝕜, F →L[𝕜] F) (fun x => φ x : B → F →L[𝕜] F) U)
      (h2φ : SmoothOn IB 𝓘(𝕜, F →L[𝕜] F) (fun x => (φ x).symm : B → F →L[𝕜] F) U),
        {e | e.EqOnSource (FiberwiseLinear.partialHomeomorph φ hU hφ.continuousOn h2φ.continuousOn)}
  trans' := by
    simp only [mem_iUnion]
    rintro e e' ⟨φ, U, hU, hφ, h2φ, heφ⟩ ⟨φ', U', hU', hφ', h2φ', heφ'⟩
    refine' ⟨fun b => (φ b).trans (φ' b), _, hU.inter hU', _, _,
      Setoid.trans (PartialHomeomorph.EqOnSource.trans' heφ heφ') ⟨_, _⟩⟩
    · show
        SmoothOn IB 𝓘(𝕜, F →L[𝕜] F)
          (fun x : B => (φ' x).toContinuousLinearMap ∘L (φ x).toContinuousLinearMap) (U ∩ U')
      exact (hφ'.mono <| inter_subset_right _ _).clm_comp (hφ.mono <| inter_subset_left _ _)
    · show
        SmoothOn IB 𝓘(𝕜, F →L[𝕜] F)
          (fun x : B => (φ x).symm.toContinuousLinearMap ∘L (φ' x).symm.toContinuousLinearMap)
          (U ∩ U')
      exact (h2φ.mono <| inter_subset_left _ _).clm_comp (h2φ'.mono <| inter_subset_right _ _)
    · apply FiberwiseLinear.source_trans_partialHomeomorph
    · rintro ⟨b, v⟩ -; apply FiberwiseLinear.trans_partialHomeomorph_apply
  -- Porting note: without introducing `e` first, the first `simp only` fails
  symm' := fun e ↦ by
    simp only [mem_iUnion]
    rintro ⟨φ, U, hU, hφ, h2φ, heφ⟩
    refine' ⟨fun b => (φ b).symm, U, hU, h2φ, _, PartialHomeomorph.EqOnSource.symm' heφ⟩
    simp_rw [ContinuousLinearEquiv.symm_symm]
    exact hφ
  id_mem' := by
    simp_rw [mem_iUnion]
    refine ⟨fun _ ↦ ContinuousLinearEquiv.refl 𝕜 F, univ, isOpen_univ, smoothOn_const,
      smoothOn_const, ⟨?_, fun b _hb ↦ rfl⟩⟩
    simp only [FiberwiseLinear.partialHomeomorph, PartialHomeomorph.refl_partialEquiv,
      PartialEquiv.refl_source, univ_prod_univ]
  locality' := by
    -- the hard work has been extracted to `locality_aux₁` and `locality_aux₂`
    simp only [mem_iUnion]
    intro e he
    obtain ⟨U, hU, h⟩ := SmoothFiberwiseLinear.locality_aux₁ e he
    exact SmoothFiberwiseLinear.locality_aux₂ e U hU h
  mem_of_eqOnSource' := by
    simp only [mem_iUnion]
    rintro e e' ⟨φ, U, hU, hφ, h2φ, heφ⟩ hee'
    exact ⟨φ, U, hU, hφ, h2φ, Setoid.trans hee' heφ⟩
#align smooth_fiberwise_linear smoothFiberwiseLinear