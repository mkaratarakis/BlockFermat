def directSum :
    ((⨁ i₁, M₁ i₁) ⊗[R] ⨁ i₂, M₂ i₂) ≃ₗ[R] ⨁ i : ι₁ × ι₂, M₁ i.1 ⊗[R] M₂ i.2 := by
  -- Porting note: entirely rewritten to allow unification to happen one step at a time
  refine LinearEquiv.ofLinear (R := R) (R₂ := R) ?toFun ?invFun ?left ?right
  · refine lift ?_
    refine DirectSum.toModule R _ _ fun i₁ => ?_
    refine LinearMap.flip ?_
    refine DirectSum.toModule R _ _ fun i₂ => LinearMap.flip <| ?_
    refine curry ?_
    exact DirectSum.lof R (ι₁ × ι₂) (fun i => M₁ i.1 ⊗[R] M₂ i.2) (i₁, i₂)
  · refine DirectSum.toModule R _ _ fun i => ?_
    exact map (DirectSum.lof R _ M₁ i.1) (DirectSum.lof R _ M₂ i.2)
  · refine DirectSum.linearMap_ext R fun ⟨i₁, i₂⟩ => ?_
    refine TensorProduct.ext ?_
    refine LinearMap.ext₂ fun m₁ m₂ => ?_
    -- Porting note: seems much nicer than the `repeat` lean 3 proof.
    simp only [compr₂_apply, comp_apply, id_apply, mk_apply, DirectSum.toModule_lof, map_tmul,
        lift.tmul, flip_apply, curry_apply]
  · -- `(_)` prevents typeclass search timing out on problems that can be solved immediately by
    -- unification
    refine TensorProduct.ext ?_
    refine DirectSum.linearMap_ext _ fun i₁ => ?_
    refine LinearMap.ext fun x₁ => ?_
    refine DirectSum.linearMap_ext _ fun i₂ => ?_
    refine LinearMap.ext fun x₂ => ?_
    -- Porting note: seems much nicer than the `repeat` lean 3 proof.
    simp only [compr₂_apply, comp_apply, id_apply, mk_apply, DirectSum.toModule_lof, map_tmul,
        lift.tmul, flip_apply, curry_apply]
  /- was:

    refine'
      LinearEquiv.ofLinear
        (lift <|
          DirectSum.toModule R _ _ fun i₁ => LinearMap.flip <| DirectSum.toModule R _ _ fun i₂ =>
                LinearMap.flip <| curry <|
                  DirectSum.lof R (ι₁ × ι₂) (fun i => M₁ i.1 ⊗[R] M₂ i.2) (i₁, i₂))
        (DirectSum.toModule R _ _ fun i => map (DirectSum.lof R _ _ _) (DirectSum.lof R _ _ _)) _
        _ <;>
    [ext ⟨i₁, i₂⟩ x₁ x₂ : 4, ext i₁ i₂ x₁ x₂ : 5]
  repeat'
    first
      |rw [compr₂_apply]|rw [comp_apply]|rw [id_apply]|rw [mk_apply]|rw [DirectSum.toModule_lof]
      |rw [map_tmul]|rw [lift.tmul]|rw [flip_apply]|rw [curry_apply]
  -/

/- alternative with explicit types:
  refine'
      LinearEquiv.ofLinear
        (lift <|
          DirectSum.toModule
            (R := R) (M := M₁) (N := (⨁ i₂, M₂ i₂) →ₗ[R] ⨁ i : ι₁ × ι₂, M₁ i.1 ⊗[R] M₂ i.2)
            (φ := fun i₁ => LinearMap.flip <|
              DirectSum.toModule (R := R) (M := M₂) (N := ⨁ i : ι₁ × ι₂, M₁ i.1 ⊗[R] M₂ i.2)
              (φ := fun i₂ => LinearMap.flip <| curry <|
                  DirectSum.lof R (ι₁ × ι₂) (fun i => M₁ i.1 ⊗[R] M₂ i.2) (i₁, i₂))))
        (DirectSum.toModule
          (R := R)
          (M := fun i : ι₁ × ι₂ => M₁ i.1 ⊗[R] M₂ i.2)
          (N := (⨁ i₁, M₁ i₁) ⊗[R] ⨁ i₂, M₂ i₂)
          (φ := fun i : ι₁ × ι₂ => map (DirectSum.lof R _ M₁ i.1) (DirectSum.lof R _ M₂ i.2))) _
        _ <;>
    [ext ⟨i₁, i₂⟩ x₁ x₂ : 4, ext i₁ i₂ x₁ x₂ : 5]
  repeat'
    first
      |rw [compr₂_apply]|rw [comp_apply]|rw [id_apply]|rw [mk_apply]|rw [DirectSum.toModule_lof]
      |rw [map_tmul]|rw [lift.tmul]|rw [flip_apply]|rw [curry_apply]
-/
#align tensor_product.direct_sum TensorProduct.directSum

def directSumLeft : (⨁ i₁, M₁ i₁) ⊗[R] M₂' ≃ₗ[R] ⨁ i, M₁ i ⊗[R] M₂' :=
  LinearEquiv.ofLinear
    (lift <|
      DirectSum.toModule R _ _ fun i =>
        (mk R _ _).compr₂ <| DirectSum.lof R ι₁ (fun i => M₁ i ⊗[R] M₂') _)
    (DirectSum.toModule R _ _ fun i => rTensor _ (DirectSum.lof R ι₁ _ _))
    (DirectSum.linearMap_ext R fun i =>
      TensorProduct.ext <|
        LinearMap.ext₂ fun m₁ m₂ => by
          dsimp only [comp_apply, compr₂_apply, id_apply, mk_apply]
          simp_rw [DirectSum.toModule_lof, rTensor_tmul, lift.tmul, DirectSum.toModule_lof,
            compr₂_apply, mk_apply])
    (TensorProduct.ext <|
      DirectSum.linearMap_ext R fun i =>
        LinearMap.ext₂ fun m₁ m₂ => by
          dsimp only [comp_apply, compr₂_apply, id_apply, mk_apply]
          simp_rw [lift.tmul, DirectSum.toModule_lof, compr₂_apply,
            mk_apply, DirectSum.toModule_lof, rTensor_tmul])
#align tensor_product.direct_sum_left TensorProduct.directSumLeft

def directSumRight : (M₁' ⊗[R] ⨁ i, M₂ i) ≃ₗ[R] ⨁ i, M₁' ⊗[R] M₂ i :=
  TensorProduct.comm R _ _ ≪≫ₗ directSumLeft R M₂ M₁' ≪≫ₗ
    DFinsupp.mapRange.linearEquiv fun _ => TensorProduct.comm R _ _
#align tensor_product.direct_sum_right TensorProduct.directSumRight