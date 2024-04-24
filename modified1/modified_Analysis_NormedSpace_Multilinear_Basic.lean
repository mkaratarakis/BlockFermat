def mkContinuous (C : ℝ) (H : ∀ m, ‖f m‖ ≤ C * ∏ i, ‖m i‖) : ContinuousMultilinearMap 𝕜 E G :=
  { f with cont := f.continuous_of_bound C H }
#align multilinear_map.mk_continuous MultilinearMap.mkContinuous

def opNorm :=
  sInf { c | 0 ≤ (c : ℝ) ∧ ∀ m, ‖f m‖ ≤ c * ∏ i, ‖m i‖ }
#align continuous_multilinear_map.op_norm ContinuousMultilinearMap.opNorm

def : ‖f‖ = sInf { c | 0 ≤ (c : ℝ) ∧ ∀ m, ‖f m‖ ≤ c * ∏ i, ‖m i‖ } :=
  rfl
#align continuous_multilinear_map.norm_def ContinuousMultilinearMap.norm_def

def seminorm : Seminorm 𝕜 (ContinuousMultilinearMap 𝕜 E G) :=
  .ofSMulLE norm opNorm_zero opNorm_add_le fun c f ↦ opNorm_smul_le f c

private lemma uniformity_eq_seminorm :
    𝓤 (ContinuousMultilinearMap 𝕜 E G) = ⨅ r > 0, 𝓟 {f | ‖f.1 - f.2‖ < r} := by
  refine (ContinuousMultilinearMap.seminorm 𝕜 E G).uniformity_eq_of_hasBasis
    (ContinuousMultilinearMap.hasBasis_nhds_zero_of_basis Metric.nhds_basis_closedBall)
    ?_ fun (s, r) ⟨hs, hr⟩ ↦ ?_
  · rcases NormedField.exists_lt_norm 𝕜 1 with ⟨c, hc⟩
    have hc₀ : 0 < ‖c‖ := one_pos.trans hc
    simp only [hasBasis_nhds_zero.mem_iff, Prod.exists]
    use 1, closedBall 0 ‖c‖, closedBall 0 1
    suffices ∀ f : ContinuousMultilinearMap 𝕜 E G, (∀ x, ‖x‖ ≤ ‖c‖ → ‖f x‖ ≤ 1) → ‖f‖ ≤ 1 by
      simpa [NormedSpace.isVonNBounded_closedBall, closedBall_mem_nhds, Set.subset_def, Set.MapsTo]
    intro f hf
    refine opNorm_le_bound _ (by positivity) <|
      f.1.bound_of_shell_of_continuous f.2 (fun _ ↦ hc₀) (fun _ ↦ hc) fun x hcx hx ↦ ?_
    calc
      ‖f x‖ ≤ 1 := hf _ <| (pi_norm_le_iff_of_nonneg (norm_nonneg c)).2 fun i ↦ (hx i).le
      _ = ∏ i : ι, 1 := by simp
      _ ≤ ∏ i, ‖x i‖ := Finset.prod_le_prod (fun _ _ ↦ zero_le_one) fun i _ ↦ by
        simpa only [div_self hc₀.ne'] using hcx i
      _ = 1 * ∏ i, ‖x i‖ := (one_mul _).symm
  · rcases (NormedSpace.isVonNBounded_iff' _ _ _).1 hs with ⟨ε, hε⟩
    rcases exists_pos_mul_lt hr (ε ^ Fintype.card ι) with ⟨δ, hδ₀, hδ⟩
    refine ⟨δ, hδ₀, fun f hf x hx ↦ ?_⟩
    simp only [Seminorm.mem_ball_zero, mem_closedBall_zero_iff] at hf ⊢
    replace hf : ‖f‖ ≤ δ := hf.le
    replace hx : ‖x‖ ≤ ε := hε x hx
    calc
      ‖f x‖ ≤ ‖f‖ * ε ^ Fintype.card ι := le_opNorm_mul_pow_card_of_le f hx
      _ ≤ δ * ε ^ Fintype.card ι := by have := (norm_nonneg x).trans hx; gcongr
      _ ≤ r := (mul_comm _ _).trans_le hδ.le

instance instPseudoMetricSpace : PseudoMetricSpace (ContinuousMultilinearMap 𝕜 E G) :=
  .replaceUniformity
    (ContinuousMultilinearMap.seminorm 𝕜 E G).toSeminormedAddCommGroup.toPseudoMetricSpace
    uniformity_eq_seminorm

/-- Continuous multilinear maps themselves form a seminormed space with respect to
    the operator norm. -/
instance seminormedAddCommGroup :
    SeminormedAddCommGroup (ContinuousMultilinearMap 𝕜 E G) := ⟨fun _ _ ↦ rfl⟩

/-- An alias of `ContinuousMultilinearMap.seminormedAddCommGroup` with non-dependent types to help
typeclass search. -/
instance seminormedAddCommGroup' :
    SeminormedAddCommGroup (ContinuousMultilinearMap 𝕜 (fun _ : ι => G) G') :=
  ContinuousMultilinearMap.seminormedAddCommGroup

instance normedSpace : NormedSpace 𝕜' (ContinuousMultilinearMap 𝕜 E G) :=
  ⟨fun c f => f.opNorm_smul_le c⟩
#align continuous_multilinear_map.normed_space ContinuousMultilinearMap.normedSpace

def ofSubsingletonₗᵢ [Subsingleton ι] (i : ι) :
    (G →L[𝕜] G') ≃ₗᵢ[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ G) G' :=
  { ofSubsingleton 𝕜 G G' i with
    map_add' := fun _ _ ↦ rfl
    map_smul' := fun _ _ ↦ rfl
    norm_map' := norm_ofSubsingleton i }

theorem norm_ofSubsingleton_id_le [Subsingleton ι] (i : ι) :
    ‖ofSubsingleton 𝕜 G G i (.id _ _)‖ ≤ 1 := by
  rw [norm_ofSubsingleton]
  apply ContinuousLinearMap.norm_id_le
#align continuous_multilinear_map.norm_of_subsingleton_le ContinuousMultilinearMap.norm_ofSubsingleton_id_le

def prodL :
    ContinuousMultilinearMap 𝕜 E G × ContinuousMultilinearMap 𝕜 E G' ≃ₗᵢ[𝕜]
      ContinuousMultilinearMap 𝕜 E (G × G') where
  toFun f := f.1.prod f.2
  invFun f :=
    ((ContinuousLinearMap.fst 𝕜 G G').compContinuousMultilinearMap f,
      (ContinuousLinearMap.snd 𝕜 G G').compContinuousMultilinearMap f)
  map_add' f g := rfl
  map_smul' c f := rfl
  left_inv f := by ext <;> rfl
  right_inv f := by ext <;> rfl
  norm_map' f := opNorm_prod f.1 f.2
set_option linter.uppercaseLean3 false in
#align continuous_multilinear_map.prodL ContinuousMultilinearMap.prodL

def piₗᵢ {ι' : Type v'} [Fintype ι'] {E' : ι' → Type wE'} [∀ i', NormedAddCommGroup (E' i')]
    [∀ i', NormedSpace 𝕜 (E' i')] :
    @LinearIsometryEquiv 𝕜 𝕜 _ _ (RingHom.id 𝕜) _ _ _ (∀ i', ContinuousMultilinearMap 𝕜 E (E' i'))
      (ContinuousMultilinearMap 𝕜 E (∀ i, E' i)) _ _ (@Pi.module ι' _ 𝕜 _ _ fun _ => inferInstance)
      _ where
  toLinearEquiv := piLinearEquiv
  norm_map' := opNorm_pi
#align continuous_multilinear_map.piₗᵢ ContinuousMultilinearMap.piₗᵢ

def restrictScalarsₗᵢ : ContinuousMultilinearMap 𝕜 E G →ₗᵢ[𝕜'] ContinuousMultilinearMap 𝕜' E G where
  toFun := restrictScalars 𝕜'
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' _ := rfl
#align continuous_multilinear_map.restrict_scalarsₗᵢ ContinuousMultilinearMap.restrictScalarsₗᵢ

def restrictScalarsLinear : ContinuousMultilinearMap 𝕜 E G →L[𝕜'] ContinuousMultilinearMap 𝕜' E G :=
  (restrictScalarsₗᵢ 𝕜').toContinuousLinearMap
#align continuous_multilinear_map.restrict_scalars_linear ContinuousMultilinearMap.restrictScalarsLinear

def restr {k n : ℕ} (f : (G[×n]→L[𝕜] G' : _)) (s : Finset (Fin n)) (hk : s.card = k) (z : G) :
    G[×k]→L[𝕜] G' :=
  (f.toMultilinearMap.restr s hk z).mkContinuous (‖f‖ * ‖z‖ ^ (n - k)) fun _ =>
    MultilinearMap.restr_norm_le _ _ _ _ f.le_opNorm _
#align continuous_multilinear_map.restr ContinuousMultilinearMap.restr

def smulRightL : ContinuousMultilinearMap 𝕜 E 𝕜 →L[𝕜] G →L[𝕜] ContinuousMultilinearMap 𝕜 E G :=
  LinearMap.mkContinuous₂
    { toFun := fun f ↦
        { toFun := fun z ↦ f.smulRight z
          map_add' := fun x y ↦ by ext; simp
          map_smul' := fun c x ↦ by ext; simp [smul_smul, mul_comm] }
      map_add' := fun f g ↦ by ext; simp [add_smul]
      map_smul' := fun c f ↦ by ext; simp [smul_smul] }
    1 (fun f z ↦ by simp [norm_smulRight])

@[simp] lemma smulRightL_apply (f : ContinuousMultilinearMap 𝕜 E 𝕜) (z : G) :
  smulRightL 𝕜 E G f z = f.smulRight z := rfl

variable (𝕜 ι G)

/-- Continuous multilinear maps on `𝕜^n` with values in `G` are in bijection with `G`, as such a
continuous multilinear map is completely determined by its value on the constant vector made of
ones. We register this bijection as a linear isometry in
`ContinuousMultilinearMap.piFieldEquiv`. -/
protected def piFieldEquiv : G ≃ₗᵢ[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : ι => 𝕜) G where
  toFun z := ContinuousMultilinearMap.mkPiRing 𝕜 ι z
  invFun f := f fun i => 1
  map_add' z z' := by
    ext m
    simp [smul_add]
  map_smul' c z := by
    ext m
    simp [smul_smul, mul_comm]
  left_inv z := by simp
  right_inv f := f.mkPiRing_apply_one_eq_self
  norm_map' := norm_mkPiRing
#align continuous_multilinear_map.pi_field_equiv ContinuousMultilinearMap.piFieldEquiv

def compContinuousMultilinearMapL :
    (G →L[𝕜] G') →L[𝕜] ContinuousMultilinearMap 𝕜 E G →L[𝕜] ContinuousMultilinearMap 𝕜 E G' :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ 𝕜 compContinuousMultilinearMap (fun f₁ f₂ g => rfl) (fun c f g => rfl)
      (fun f g₁ g₂ => by ext1; apply f.map_add)
      (fun c f g => by ext1; simp))
    1
    fun f g => by rw [one_mul]; exact f.norm_compContinuousMultilinearMap_le g
#align continuous_linear_map.comp_continuous_multilinear_mapL ContinuousLinearMap.compContinuousMultilinearMapL

def _root_.ContinuousLinearEquiv.compContinuousMultilinearMapL (g : G ≃L[𝕜] G') :
    ContinuousMultilinearMap 𝕜 E G ≃L[𝕜] ContinuousMultilinearMap 𝕜 E G' :=
  { compContinuousMultilinearMapL 𝕜 E G G' g.toContinuousLinearMap with
    invFun := compContinuousMultilinearMapL 𝕜 E G' G g.symm.toContinuousLinearMap
    left_inv := by
      intro f
      ext1 m
      simp [compContinuousMultilinearMapL]
    right_inv := by
      intro f
      ext1 m
      simp [compContinuousMultilinearMapL]
    continuous_toFun := (compContinuousMultilinearMapL 𝕜 E G G' g.toContinuousLinearMap).continuous
    continuous_invFun :=
      (compContinuousMultilinearMapL 𝕜 E G' G g.symm.toContinuousLinearMap).continuous }
#align continuous_linear_equiv.comp_continuous_multilinear_mapL ContinuousLinearEquiv.compContinuousMultilinearMapL

def flipMultilinear (f : G →L[𝕜] ContinuousMultilinearMap 𝕜 E G') :
    ContinuousMultilinearMap 𝕜 E (G →L[𝕜] G') :=
  MultilinearMap.mkContinuous
    { toFun := fun m =>
        LinearMap.mkContinuous
          { toFun := fun x => f x m
            map_add' := fun x y => by simp only [map_add, ContinuousMultilinearMap.add_apply]
            map_smul' := fun c x => by
              simp only [ContinuousMultilinearMap.smul_apply, map_smul, RingHom.id_apply] }
          (‖f‖ * ∏ i, ‖m i‖) fun x => by
          rw [mul_right_comm]
          exact (f x).le_of_opNorm_le _ (f.le_opNorm x)
      map_add' := fun m i x y => by
        ext1
        simp only [add_apply, ContinuousMultilinearMap.map_add, LinearMap.coe_mk,
          LinearMap.mkContinuous_apply, AddHom.coe_mk]
      map_smul' := fun m i c x => by
        ext1
        simp only [coe_smul', ContinuousMultilinearMap.map_smul, LinearMap.coe_mk,
          LinearMap.mkContinuous_apply, Pi.smul_apply, AddHom.coe_mk] }
    ‖f‖ fun m => by
      dsimp only [MultilinearMap.coe_mk]
      refine LinearMap.mkContinuous_norm_le _
        (mul_nonneg (norm_nonneg f) (prod_nonneg fun i _ => norm_nonneg (m i))) _
#align continuous_linear_map.flip_multilinear ContinuousLinearMap.flipMultilinear

def mkContinuousLinear (f : G →ₗ[𝕜] MultilinearMap 𝕜 E G') (C : ℝ)
    (H : ∀ x m, ‖f x m‖ ≤ C * ‖x‖ * ∏ i, ‖m i‖) : G →L[𝕜] ContinuousMultilinearMap 𝕜 E G' :=
  LinearMap.mkContinuous
    { toFun := fun x => (f x).mkContinuous (C * ‖x‖) <| H x
      map_add' := fun x y => by
        ext1
        simp only [_root_.map_add]
        rfl
      map_smul' := fun c x => by
        ext1
        simp only [_root_.map_smul]
        rfl }
    (max C 0) fun x => by
      rw [LinearMap.coe_mk, AddHom.coe_mk] -- Porting note: added
      exact ((f x).mkContinuous_norm_le' _).trans_eq <| by
        rw [max_mul_of_nonneg _ _ (norm_nonneg x), zero_mul]
#align multilinear_map.mk_continuous_linear MultilinearMap.mkContinuousLinear

def mkContinuousMultilinear (f : MultilinearMap 𝕜 E (MultilinearMap 𝕜 E' G)) (C : ℝ)
    (H : ∀ m₁ m₂, ‖f m₁ m₂‖ ≤ (C * ∏ i, ‖m₁ i‖) * ∏ i, ‖m₂ i‖) :
    ContinuousMultilinearMap 𝕜 E (ContinuousMultilinearMap 𝕜 E' G) :=
  mkContinuous
    { toFun := fun m => mkContinuous (f m) (C * ∏ i, ‖m i‖) <| H m
      map_add' := fun m i x y => by
        ext1
        simp
      map_smul' := fun m i c x => by
        ext1
        simp }
    (max C 0) fun m => by
      simp only [coe_mk]
      refine ((f m).mkContinuous_norm_le' _).trans_eq ?_
      rw [max_mul_of_nonneg, zero_mul]
      exact prod_nonneg fun _ _ => norm_nonneg _
#align multilinear_map.mk_continuous_multilinear MultilinearMap.mkContinuousMultilinear

def compContinuousLinearMapL (f : ∀ i, E i →L[𝕜] E₁ i) :
    ContinuousMultilinearMap 𝕜 E₁ G →L[𝕜] ContinuousMultilinearMap 𝕜 E G :=
  LinearMap.mkContinuous
    { toFun := fun g => g.compContinuousLinearMap f
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    (∏ i, ‖f i‖)
    fun _ => (norm_compContinuousLinearMap_le _ _).trans_eq (mul_comm _ _)
#align continuous_multilinear_map.comp_continuous_linear_mapL ContinuousMultilinearMap.compContinuousLinearMapL

def compContinuousLinearMapLRight (g : ContinuousMultilinearMap 𝕜 E₁ G) :
    ContinuousMultilinearMap 𝕜 (fun i ↦ E i →L[𝕜] E₁ i) (ContinuousMultilinearMap 𝕜 E G) :=
  MultilinearMap.mkContinuous
    { toFun := fun f => g.compContinuousLinearMap f
      map_add' := by
        intro h f i f₁ f₂
        ext x
        simp only [compContinuousLinearMap_apply, add_apply]
        convert g.map_add (fun j ↦ f j (x j)) i (f₁ (x i)) (f₂ (x i)) <;>
          exact apply_update (fun (i : ι) (f : E i →L[𝕜] E₁ i) ↦ f (x i)) f i _ _
      map_smul' := by
        intro h f i a f₀
        ext x
        simp only [compContinuousLinearMap_apply, smul_apply]
        convert g.map_smul (fun j ↦ f j (x j)) i a (f₀ (x i)) <;>
          exact apply_update (fun (i : ι) (f : E i →L[𝕜] E₁ i) ↦ f (x i)) f i _ _ }
    (‖g‖) (fun f ↦ by simp [norm_compContinuousLinearMap_le])

@[simp]
theorem compContinuousLinearMapLRight_apply (g : ContinuousMultilinearMap 𝕜 E₁ G)
    (f : ∀ i, E i →L[𝕜] E₁ i) : compContinuousLinearMapLRight g f = g.compContinuousLinearMap f :=
  rfl

variable (E) in
theorem norm_compContinuousLinearMapLRight_le (g : ContinuousMultilinearMap 𝕜 E₁ G) :
    ‖compContinuousLinearMapLRight (E := E) g‖ ≤ ‖g‖ :=
  MultilinearMap.mkContinuous_norm_le _ (norm_nonneg _) _

variable (𝕜 E E₁ G)

open Function in
/-- If `f` is a collection of continuous linear maps, then the construction
`ContinuousMultilinearMap.compContinuousLinearMap`
sending a continuous multilinear map `g` to `g (f₁ ·, ..., fₙ ·)`
is continuous-linear in `g` and multilinear in `f₁, ..., fₙ`. -/
noncomputable def compContinuousLinearMapMultilinear :
    MultilinearMap 𝕜 (fun i ↦ E i →L[𝕜] E₁ i)
      ((ContinuousMultilinearMap 𝕜 E₁ G) →L[𝕜] ContinuousMultilinearMap 𝕜 E G) where
  toFun := compContinuousLinearMapL
  map_add' f i f₁ f₂ := by
    ext g x
    change (g fun j ↦ update f i (f₁ + f₂) j <| x j) =
        (g fun j ↦ update f i f₁ j <| x j) + g fun j ↦ update f i f₂ j (x j)
    convert g.map_add (fun j ↦ f j (x j)) i (f₁ (x i)) (f₂ (x i)) <;>
      exact apply_update (fun (i : ι) (f : E i →L[𝕜] E₁ i) ↦ f (x i)) f i _ _
  map_smul' f i a f₀ := by
    ext g x
    change (g fun j ↦ update f i (a • f₀) j <| x j) = a • g fun j ↦ update f i f₀ j (x j)
    convert g.map_smul (fun j ↦ f j (x j)) i a (f₀ (x i)) <;>
      exact apply_update (fun (i : ι) (f : E i →L[𝕜] E₁ i) ↦ f (x i)) f i _ _

/-- If `f` is a collection of continuous linear maps, then the construction
`ContinuousMultilinearMap.compContinuousLinearMap`
sending a continuous multilinear map `g` to `g (f₁ ·, ..., fₙ ·)` is continuous-linear in `g` and
continuous-multilinear in `f₁, ..., fₙ`. -/
noncomputable def compContinuousLinearMapContinuousMultilinear :
    ContinuousMultilinearMap 𝕜 (fun i ↦ E i →L[𝕜] E₁ i)
      ((ContinuousMultilinearMap 𝕜 E₁ G) →L[𝕜] ContinuousMultilinearMap 𝕜 E G) :=
  @MultilinearMap.mkContinuous 𝕜 ι (fun i ↦ E i →L[𝕜] E₁ i)
    ((ContinuousMultilinearMap 𝕜 E₁ G) →L[𝕜] ContinuousMultilinearMap 𝕜 E G) _ _
    (fun _ ↦ ContinuousLinearMap.toSeminormedAddCommGroup)
    (fun _ ↦ ContinuousLinearMap.toNormedSpace) _ _
    (compContinuousLinearMapMultilinear 𝕜 E E₁ G) 1
    fun f ↦ by simpa using norm_compContinuousLinearMapL_le G f

variable {𝕜 E E₁}

/-- `ContinuousMultilinearMap.compContinuousLinearMap` as a bundled continuous linear equiv,
given `f : Π i, E i ≃L[𝕜] E₁ i`. -/
def compContinuousLinearMapEquivL (f : ∀ i, E i ≃L[𝕜] E₁ i) :
    ContinuousMultilinearMap 𝕜 E₁ G ≃L[𝕜] ContinuousMultilinearMap 𝕜 E G :=
  { compContinuousLinearMapL fun i => (f i : E i →L[𝕜] E₁ i) with
    invFun := compContinuousLinearMapL fun i => ((f i).symm : E₁ i →L[𝕜] E i)
    continuous_toFun := (compContinuousLinearMapL fun i => (f i : E i →L[𝕜] E₁ i)).continuous
    continuous_invFun :=
      (compContinuousLinearMapL fun i => ((f i).symm : E₁ i →L[𝕜] E i)).continuous
    left_inv := by
      intro g
      ext1 m
      simp only [LinearMap.toFun_eq_coe, ContinuousLinearMap.coe_coe,
        compContinuousLinearMapL_apply, compContinuousLinearMap_apply,
        ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
    right_inv := by
      intro g
      ext1 m
      simp only [compContinuousLinearMapL_apply, LinearMap.toFun_eq_coe,
        ContinuousLinearMap.coe_coe, compContinuousLinearMap_apply,
        ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply] }
#align continuous_multilinear_map.comp_continuous_linear_map_equivL ContinuousMultilinearMap.compContinuousLinearMapEquivL

structure on `ContinuousMultilinearMap 𝕜 E G`.
-/


namespace ContinuousMultilinearMap

variable (c : 𝕜) (f g : ContinuousMultilinearMap 𝕜 E G) (m : ∀ i, E i)

theorem bound : ∃ C : ℝ, 0 < C ∧ ∀ m, ‖f m‖ ≤ C * ∏ i, ‖m i‖ :=
  f.toMultilinearMap.exists_bound_of_continuous f.2
#align continuous_multilinear_map.bound ContinuousMultilinearMap.bound

structure on `ContinuousMultilinearMap 𝕜 E G`,
but we have to override the projection `UniformSpace`
so that it is definitionally equal to the one coming from the topologies on `E` and `G`. -/
protected def seminorm : Seminorm 𝕜 (ContinuousMultilinearMap 𝕜 E G) :=
  .ofSMulLE norm opNorm_zero opNorm_add_le fun c f ↦ opNorm_smul_le f c

private lemma uniformity_eq_seminorm :
    𝓤 (ContinuousMultilinearMap 𝕜 E G) = ⨅ r > 0, 𝓟 {f | ‖f.1 - f.2‖ < r} := by
  refine (ContinuousMultilinearMap.seminorm 𝕜 E G).uniformity_eq_of_hasBasis
    (ContinuousMultilinearMap.hasBasis_nhds_zero_of_basis Metric.nhds_basis_closedBall)
    ?_ fun (s, r) ⟨hs, hr⟩ ↦ ?_
  · rcases NormedField.exists_lt_norm 𝕜 1 with ⟨c, hc⟩
    have hc₀ : 0 < ‖c‖ := one_pos.trans hc
    simp only [hasBasis_nhds_zero.mem_iff, Prod.exists]
    use 1, closedBall 0 ‖c‖, closedBall 0 1
    suffices ∀ f : ContinuousMultilinearMap 𝕜 E G, (∀ x, ‖x‖ ≤ ‖c‖ → ‖f x‖ ≤ 1) → ‖f‖ ≤ 1 by
      simpa [NormedSpace.isVonNBounded_closedBall, closedBall_mem_nhds, Set.subset_def, Set.MapsTo]
    intro f hf
    refine opNorm_le_bound _ (by positivity) <|
      f.1.bound_of_shell_of_continuous f.2 (fun _ ↦ hc₀) (fun _ ↦ hc) fun x hcx hx ↦ ?_
    calc
      ‖f x‖ ≤ 1 := hf _ <| (pi_norm_le_iff_of_nonneg (norm_nonneg c)).2 fun i ↦ (hx i).le
      _ = ∏ i : ι, 1 := by simp
      _ ≤ ∏ i, ‖x i‖ := Finset.prod_le_prod (fun _ _ ↦ zero_le_one) fun i _ ↦ by
        simpa only [div_self hc₀.ne'] using hcx i
      _ = 1 * ∏ i, ‖x i‖ := (one_mul _).symm
  · rcases (NormedSpace.isVonNBounded_iff' _ _ _).1 hs with ⟨ε, hε⟩
    rcases exists_pos_mul_lt hr (ε ^ Fintype.card ι) with ⟨δ, hδ₀, hδ⟩
    refine ⟨δ, hδ₀, fun f hf x hx ↦ ?_⟩
    simp only [Seminorm.mem_ball_zero, mem_closedBall_zero_iff] at hf ⊢
    replace hf : ‖f‖ ≤ δ := hf.le
    replace hx : ‖x‖ ≤ ε := hε x hx
    calc
      ‖f x‖ ≤ ‖f‖ * ε ^ Fintype.card ι := le_opNorm_mul_pow_card_of_le f hx
      _ ≤ δ * ε ^ Fintype.card ι := by have := (norm_nonneg x).trans hx; gcongr
      _ ≤ r := (mul_comm _ _).trans_le hδ.le

instance instPseudoMetricSpace : PseudoMetricSpace (ContinuousMultilinearMap 𝕜 E G) :=
  .replaceUniformity
    (ContinuousMultilinearMap.seminorm 𝕜 E G).toSeminormedAddCommGroup.toPseudoMetricSpace
    uniformity_eq_seminorm

/-- Continuous multilinear maps themselves form a seminormed space with respect to
    the operator norm. -/
instance seminormedAddCommGroup :
    SeminormedAddCommGroup (ContinuousMultilinearMap 𝕜 E G) := ⟨fun _ _ ↦ rfl⟩

/-- An alias of `ContinuousMultilinearMap.seminormedAddCommGroup` with non-dependent types to help
typeclass search. -/
instance seminormedAddCommGroup' :
    SeminormedAddCommGroup (ContinuousMultilinearMap 𝕜 (fun _ : ι => G) G') :=
  ContinuousMultilinearMap.seminormedAddCommGroup

instance normedSpace : NormedSpace 𝕜' (ContinuousMultilinearMap 𝕜 E G) :=
  ⟨fun c f => f.opNorm_smul_le c⟩
#align continuous_multilinear_map.normed_space ContinuousMultilinearMap.normedSpace