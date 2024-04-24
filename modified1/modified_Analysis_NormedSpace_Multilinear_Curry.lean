def ContinuousLinearMap.uncurryLeft
    (f : Ei 0 →L[𝕜] ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei i.succ) G) :
    ContinuousMultilinearMap 𝕜 Ei G :=
  (@LinearMap.uncurryLeft 𝕜 n Ei G _ _ _ _ _
      (ContinuousMultilinearMap.toMultilinearMapLinear.comp f.toLinearMap)).mkContinuous
    ‖f‖ fun m => by exact ContinuousLinearMap.norm_map_tail_le f m
#align continuous_linear_map.uncurry_left ContinuousLinearMap.uncurryLeft

def ContinuousMultilinearMap.curryLeft (f : ContinuousMultilinearMap 𝕜 Ei G) :
    Ei 0 →L[𝕜] ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei i.succ) G :=
  LinearMap.mkContinuous
    { -- define a linear map into `n` continuous multilinear maps
      -- from an `n+1` continuous multilinear map
      toFun := fun x =>
        (f.toMultilinearMap.curryLeft x).mkContinuous (‖f‖ * ‖x‖) (f.norm_map_cons_le x)
      map_add' := fun x y => by
        ext m
        exact f.cons_add m x y
      map_smul' := fun c x => by
        ext m
        exact
          f.cons_smul m c x }-- then register its continuity thanks to its boundedness properties.
    ‖f‖ fun x => by
      rw [LinearMap.coe_mk, AddHom.coe_mk]
      exact MultilinearMap.mkContinuous_norm_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) _
#align continuous_multilinear_map.curry_left ContinuousMultilinearMap.curryLeft

def continuousMultilinearCurryLeftEquiv :
    (Ei 0 →L[𝕜] ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei i.succ) G) ≃ₗᵢ[𝕜]
      ContinuousMultilinearMap 𝕜 Ei G :=
  LinearIsometryEquiv.ofBounds
    { toFun := ContinuousLinearMap.uncurryLeft
      map_add' := fun f₁ f₂ => by
        ext m
        rfl
      map_smul' := fun c f => by
        ext m
        rfl
      invFun := ContinuousMultilinearMap.curryLeft
      left_inv := ContinuousLinearMap.curry_uncurryLeft
      right_inv := ContinuousMultilinearMap.uncurry_curryLeft }
    (fun f => by
      simp only [LinearEquiv.coe_mk]
      exact MultilinearMap.mkContinuous_norm_le _ (norm_nonneg f) _)
    (fun f => by
      simp only [LinearEquiv.coe_symm_mk]
      exact LinearMap.mkContinuous_norm_le _ (norm_nonneg f) _)
#align continuous_multilinear_curry_left_equiv continuousMultilinearCurryLeftEquiv

def ContinuousMultilinearMap.uncurryRight
    (f : ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei <| castSucc i) (Ei (last n) →L[𝕜] G)) :
    ContinuousMultilinearMap 𝕜 Ei G :=
  let f' : MultilinearMap 𝕜 (fun i : Fin n => Ei <| castSucc i) (Ei (last n) →ₗ[𝕜] G) :=
    { toFun := fun m => (f m).toLinearMap
      map_add' := fun m i x y => by simp
      map_smul' := fun m i c x => by simp }
  (@MultilinearMap.uncurryRight 𝕜 n Ei G _ _ _ _ _ f').mkContinuous ‖f‖ fun m =>
    f.norm_map_init_le m
#align continuous_multilinear_map.uncurry_right ContinuousMultilinearMap.uncurryRight

def ContinuousMultilinearMap.curryRight (f : ContinuousMultilinearMap 𝕜 Ei G) :
    ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei <| castSucc i) (Ei (last n) →L[𝕜] G) :=
  let f' : MultilinearMap 𝕜 (fun i : Fin n => Ei <| castSucc i) (Ei (last n) →L[𝕜] G) :=
    { toFun := fun m =>
        (f.toMultilinearMap.curryRight m).mkContinuous (‖f‖ * ∏ i, ‖m i‖) fun x =>
          f.norm_map_snoc_le m x
      map_add' := fun m i x y => by
        ext
        simp
      map_smul' := fun m i c x => by
        ext
        simp }
  f'.mkContinuous ‖f‖ fun m => by
    simp only [f', MultilinearMap.coe_mk]
    exact LinearMap.mkContinuous_norm_le _
      (mul_nonneg (norm_nonneg _) (prod_nonneg fun _ _ => norm_nonneg _)) _
#align continuous_multilinear_map.curry_right ContinuousMultilinearMap.curryRight

def continuousMultilinearCurryRightEquiv :
    ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei <| castSucc i) (Ei (last n) →L[𝕜] G) ≃ₗᵢ[𝕜]
      ContinuousMultilinearMap 𝕜 Ei G :=
  LinearIsometryEquiv.ofBounds
    { toFun := ContinuousMultilinearMap.uncurryRight
      map_add' := fun f₁ f₂ => by
        ext m
        rfl
      map_smul' := fun c f => by
        ext m
        rfl
      invFun := ContinuousMultilinearMap.curryRight
      left_inv := ContinuousMultilinearMap.curry_uncurryRight
      right_inv := ContinuousMultilinearMap.uncurry_curryRight } (fun f => by
        simp only [uncurryRight, LinearEquiv.coe_mk]
        exact MultilinearMap.mkContinuous_norm_le _ (norm_nonneg f) _) fun f => by
          simp only [curryRight, LinearEquiv.coe_symm_mk]
          exact MultilinearMap.mkContinuous_norm_le _ (norm_nonneg f) _
#align continuous_multilinear_curry_right_equiv continuousMultilinearCurryRightEquiv

def continuousMultilinearCurryRightEquiv' : (G[×n]→L[𝕜] G →L[𝕜] G') ≃ₗᵢ[𝕜] G[×n.succ]→L[𝕜] G' :=
  continuousMultilinearCurryRightEquiv 𝕜 (fun _ => G) G'
#align continuous_multilinear_curry_right_equiv' continuousMultilinearCurryRightEquiv'

def ContinuousMultilinearMap.uncurry0 (f : ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => G) G') :
    G' :=
  f 0
#align continuous_multilinear_map.uncurry0 ContinuousMultilinearMap.uncurry0

def ContinuousMultilinearMap.curry0 (x : G') : G[×0]→L[𝕜] G' :=
  ContinuousMultilinearMap.constOfIsEmpty 𝕜 _ x
#align continuous_multilinear_map.curry0 ContinuousMultilinearMap.curry0

def continuousMultilinearCurryFin0 : (G[×0]→L[𝕜] G') ≃ₗᵢ[𝕜] G' where
  toFun f := ContinuousMultilinearMap.uncurry0 f
  invFun f := ContinuousMultilinearMap.curry0 𝕜 G f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv := ContinuousMultilinearMap.uncurry0_curry0
  right_inv := ContinuousMultilinearMap.curry0_uncurry0 𝕜 G
  norm_map' := ContinuousMultilinearMap.uncurry0_norm
#align continuous_multilinear_curry_fin0 continuousMultilinearCurryFin0

def continuousMultilinearCurryFin1 : (G[×1]→L[𝕜] G') ≃ₗᵢ[𝕜] G →L[𝕜] G' :=
  (continuousMultilinearCurryRightEquiv 𝕜 (fun _ : Fin 1 => G) G').symm.trans
    (continuousMultilinearCurryFin0 𝕜 G (G →L[𝕜] G'))
#align continuous_multilinear_curry_fin1 continuousMultilinearCurryFin1

def domDomCongrₗᵢ (σ : ι ≃ ι') :
    ContinuousMultilinearMap 𝕜 (fun _ : ι => G) G' ≃ₗᵢ[𝕜]
      ContinuousMultilinearMap 𝕜 (fun _ : ι' => G) G' :=
  { domDomCongrEquiv σ with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
    norm_map' := norm_domDomCongr 𝕜 G G' σ }
#align continuous_multilinear_map.dom_dom_congrₗᵢ ContinuousMultilinearMap.domDomCongrₗᵢ

def currySum (f : ContinuousMultilinearMap 𝕜 (fun _ : Sum ι ι' => G) G') :
    ContinuousMultilinearMap 𝕜 (fun _ : ι => G) (ContinuousMultilinearMap 𝕜 (fun _ : ι' => G) G') :=
  MultilinearMap.mkContinuousMultilinear (MultilinearMap.currySum f.toMultilinearMap) ‖f‖
    fun m m' => by simpa [Fintype.prod_sum_type, mul_assoc] using f.le_opNorm (Sum.elim m m')
#align continuous_multilinear_map.curry_sum ContinuousMultilinearMap.currySum

def uncurrySum (f : ContinuousMultilinearMap 𝕜 (fun _ : ι => G)
    (ContinuousMultilinearMap 𝕜 (fun _ : ι' => G) G')) :
    ContinuousMultilinearMap 𝕜 (fun _ : Sum ι ι' => G) G' :=
  MultilinearMap.mkContinuous
    (toMultilinearMapLinear.compMultilinearMap f.toMultilinearMap).uncurrySum ‖f‖ fun m => by
    simpa [Fintype.prod_sum_type, mul_assoc] using
      (f (m ∘ Sum.inl)).le_of_opNorm_le (m ∘ Sum.inr) (f.le_opNorm _)
#align continuous_multilinear_map.uncurry_sum ContinuousMultilinearMap.uncurrySum

def currySumEquiv : ContinuousMultilinearMap 𝕜 (fun _ : Sum ι ι' => G) G' ≃ₗᵢ[𝕜]
    ContinuousMultilinearMap 𝕜 (fun _ : ι => G) (ContinuousMultilinearMap 𝕜 (fun _ : ι' => G) G') :=
  LinearIsometryEquiv.ofBounds
    { toFun := currySum
      invFun := uncurrySum
      map_add' := fun f g => by
        ext
        rfl
      map_smul' := fun c f => by
        ext
        rfl
      left_inv := fun f => by
        ext m
        exact congr_arg f (Sum.elim_comp_inl_inr m)
      right_inv := fun f => by
        ext m₁ m₂
        rfl }
    (fun f => MultilinearMap.mkContinuousMultilinear_norm_le _ (norm_nonneg f) _) fun f => by
      simp only [LinearEquiv.coe_symm_mk]
      exact MultilinearMap.mkContinuous_norm_le _ (norm_nonneg f) _
#align continuous_multilinear_map.curry_sum_equiv ContinuousMultilinearMap.currySumEquiv

def curryFinFinset {k l n : ℕ} {s : Finset (Fin n)} (hk : s.card = k) (hl : sᶜ.card = l) :
    (G[×n]→L[𝕜] G') ≃ₗᵢ[𝕜] G[×k]→L[𝕜] G[×l]→L[𝕜] G' :=
  (domDomCongrₗᵢ 𝕜 G G' (finSumEquivOfFinset hk hl).symm).trans
    (currySumEquiv 𝕜 (Fin k) (Fin l) G G')
#align continuous_multilinear_map.curry_fin_finset ContinuousMultilinearMap.curryFinFinset