def Simps.apply (h : α →ᵇ β) : α → β := h
#align bounded_continuous_function.simps.apply BoundedContinuousFunction.Simps.apply

def mkOfBound (f : C(α, β)) (C : ℝ) (h : ∀ x y : α, dist (f x) (f y) ≤ C) : α →ᵇ β :=
  ⟨f, ⟨C, h⟩⟩
#align bounded_continuous_function.mk_of_bound BoundedContinuousFunction.mkOfBound

def mkOfCompact [CompactSpace α] (f : C(α, β)) : α →ᵇ β :=
  ⟨f, isBounded_range_iff.1 (isCompact_range f.continuous).isBounded⟩
#align bounded_continuous_function.mk_of_compact BoundedContinuousFunction.mkOfCompact

def mkOfDiscrete [DiscreteTopology α] (f : α → β) (C : ℝ) (h : ∀ x y : α, dist (f x) (f y) ≤ C) :
    α →ᵇ β :=
  ⟨⟨f, continuous_of_discreteTopology⟩, ⟨C, h⟩⟩
#align bounded_continuous_function.mk_of_discrete BoundedContinuousFunction.mkOfDiscrete

def const (b : β) : α →ᵇ β :=
  ⟨ContinuousMap.const α b, 0, by simp [le_rfl]⟩
#align bounded_continuous_function.const BoundedContinuousFunction.const

def compContinuous {δ : Type*} [TopologicalSpace δ] (f : α →ᵇ β) (g : C(δ, α)) : δ →ᵇ β where
  toContinuousMap := f.1.comp g
  map_bounded' := f.map_bounded'.imp fun _ hC _ _ => hC _ _
#align bounded_continuous_function.comp_continuous BoundedContinuousFunction.compContinuous

def restrict (f : α →ᵇ β) (s : Set α) : s →ᵇ β :=
  f.compContinuous <| (ContinuousMap.id _).restrict s
#align bounded_continuous_function.restrict BoundedContinuousFunction.restrict

def comp (G : β → γ) {C : ℝ≥0} (H : LipschitzWith C G) (f : α →ᵇ β) : α →ᵇ γ :=
  ⟨⟨fun x => G (f x), H.continuous.comp f.continuous⟩,
    let ⟨D, hD⟩ := f.bounded
    ⟨max C 0 * D, fun x y =>
      calc
        dist (G (f x)) (G (f y)) ≤ C * dist (f x) (f y) := H.dist_le_mul _ _
        _ ≤ max C 0 * dist (f x) (f y) := by gcongr; apply le_max_left
        _ ≤ max C 0 * D := by gcongr; apply hD
        ⟩⟩
#align bounded_continuous_function.comp BoundedContinuousFunction.comp

def codRestrict (s : Set β) (f : α →ᵇ β) (H : ∀ x, f x ∈ s) : α →ᵇ s :=
  ⟨⟨s.codRestrict f H, f.continuous.subtype_mk _⟩, f.bounded⟩
#align bounded_continuous_function.cod_restrict BoundedContinuousFunction.codRestrict

def extend (f : α ↪ δ) (g : α →ᵇ β) (h : δ →ᵇ β) : δ →ᵇ β where
  toFun := extend f g h
  continuous_toFun := continuous_of_discreteTopology
  map_bounded' := by
    rw [← isBounded_range_iff, range_extend f.injective]
    exact g.isBounded_range.union (h.isBounded_image _)
#align bounded_continuous_function.extend BoundedContinuousFunction.extend

def coeFnAddHom : (α →ᵇ β) →+ α → β where
  toFun := (⇑)
  map_zero' := coe_zero
  map_add' := coe_add
#align bounded_continuous_function.coe_fn_add_hom BoundedContinuousFunction.coeFnAddHom

def toContinuousMapAddHom : (α →ᵇ β) →+ C(α, β) where
  toFun := toContinuousMap
  map_zero' := rfl
  map_add' := by
    intros
    ext
    simp
#align bounded_continuous_function.to_continuous_map_add_hom BoundedContinuousFunction.toContinuousMapAddHom

def : ‖f‖ = dist f 0 := rfl
#align bounded_continuous_function.norm_def BoundedContinuousFunction.norm_def

def ofNormedAddCommGroup {α : Type u} {β : Type v} [TopologicalSpace α] [SeminormedAddCommGroup β]
    (f : α → β) (Hf : Continuous f) (C : ℝ) (H : ∀ x, ‖f x‖ ≤ C) : α →ᵇ β :=
  ⟨⟨fun n => f n, Hf⟩, ⟨_, dist_le_two_norm' H⟩⟩
#align bounded_continuous_function.of_normed_add_comm_group BoundedContinuousFunction.ofNormedAddCommGroup

def ofNormedAddCommGroupDiscrete {α : Type u} {β : Type v} [TopologicalSpace α] [DiscreteTopology α]
    [SeminormedAddCommGroup β] (f : α → β) (C : ℝ) (H : ∀ x, norm (f x) ≤ C) : α →ᵇ β :=
  ofNormedAddCommGroup f continuous_of_discreteTopology C H
#align bounded_continuous_function.of_normed_add_comm_group_discrete BoundedContinuousFunction.ofNormedAddCommGroupDiscrete

def normComp : α →ᵇ ℝ :=
  f.comp norm lipschitzWith_one_norm
#align bounded_continuous_function.norm_comp BoundedContinuousFunction.normComp

def : ‖f‖₊ = nndist f 0 := rfl
#align bounded_continuous_function.nnnorm_def BoundedContinuousFunction.nnnorm_def

def evalCLM (x : α) : (α →ᵇ β) →L[𝕜] β where
  toFun f := f x
  map_add' f g := add_apply _ _
  map_smul' c f := smul_apply _ _ _
#align bounded_continuous_function.eval_clm BoundedContinuousFunction.evalCLM

def toContinuousMapLinearMap : (α →ᵇ β) →ₗ[𝕜] C(α, β) where
  toFun := toContinuousMap
  map_smul' _ _ := rfl
  map_add' _ _ := rfl
#align bounded_continuous_function.to_continuous_map_linear_map BoundedContinuousFunction.toContinuousMapLinearMap

def _root_.ContinuousLinearMap.compLeftContinuousBounded (g : β →L[𝕜] γ) :
    (α →ᵇ β) →L[𝕜] α →ᵇ γ :=
  LinearMap.mkContinuous
    { toFun := fun f =>
        ofNormedAddCommGroup (g ∘ f) (g.continuous.comp f.continuous) (‖g‖ * ‖f‖) fun x =>
          g.le_opNorm_of_le (f.norm_coe_le_norm x)
      map_add' := fun f g => by ext; simp
      map_smul' := fun c f => by ext; simp } ‖g‖ fun f =>
        norm_ofNormedAddCommGroup_le _ (mul_nonneg (norm_nonneg g) (norm_nonneg f))
          (fun x => by exact g.le_opNorm_of_le (f.norm_coe_le_norm x))
#align continuous_linear_map.comp_left_continuous_bounded ContinuousLinearMap.compLeftContinuousBounded

def C : 𝕜 →+* α →ᵇ γ where
  toFun := fun c : 𝕜 => const α ((algebraMap 𝕜 γ) c)
  map_one' := ext fun _ => (algebraMap 𝕜 γ).map_one
  map_mul' _ _ := ext fun _ => (algebraMap 𝕜 γ).map_mul _ _
  map_zero' := ext fun _ => (algebraMap 𝕜 γ).map_zero
  map_add' _ _ := ext fun _ => (algebraMap 𝕜 γ).map_add _ _
set_option linter.uppercaseLean3 false in
#align bounded_continuous_function.C BoundedContinuousFunction.C

def nnrealPart (f : α →ᵇ ℝ) : α →ᵇ ℝ≥0 :=
  BoundedContinuousFunction.comp _ (show LipschitzWith 1 Real.toNNReal from lipschitzWith_posPart) f
#align bounded_continuous_function.nnreal_part BoundedContinuousFunction.nnrealPart

def nnnorm (f : α →ᵇ ℝ) : α →ᵇ ℝ≥0 :=
  BoundedContinuousFunction.comp _
    (show LipschitzWith 1 fun x : ℝ => ‖x‖₊ from lipschitzWith_one_norm) f
#align bounded_continuous_function.nnnorm BoundedContinuousFunction.nnnorm

structure BoundedContinuousFunction (α : Type u) (β : Type v) [TopologicalSpace α]
    [PseudoMetricSpace β] extends ContinuousMap α β : Type max u v where
  map_bounded' : ∃ C, ∀ x y, dist (toFun x) (toFun y) ≤ C
#align bounded_continuous_function BoundedContinuousFunction

structure

In this section, if `β` is a metric space and a `𝕜`-module whose addition and scalar multiplication
are compatible with the metric structure, then we show that the space of bounded continuous
functions from `α` to `β` inherits a so-called `BoundedSMul` structure (in particular, a
`ContinuousMul` structure, which is the mathlib formulation of being a topological module), by
using pointwise operations and checking that they are compatible with the uniform distance. -/


variable {𝕜 : Type*} [PseudoMetricSpace 𝕜] [TopologicalSpace α] [PseudoMetricSpace β]

section SMul

variable [Zero 𝕜] [Zero β] [SMul 𝕜 β] [BoundedSMul 𝕜 β]

instance instSMul : SMul 𝕜 (α →ᵇ β) where
  smul c f :=
    { toContinuousMap := c • f.toContinuousMap
      map_bounded' :=
        let ⟨b, hb⟩ := f.bounded
        ⟨dist c 0 * b, fun x y => by
          refine' (dist_smul_pair c (f x) (f y)).trans _
          refine' mul_le_mul_of_nonneg_left _ dist_nonneg
          exact hb x y⟩ }

@[simp]
theorem coe_smul (c : 𝕜) (f : α →ᵇ β) : ⇑(c • f) = fun x => c • f x := rfl
#align bounded_continuous_function.coe_smul BoundedContinuousFunction.coe_smul

structure

In this section, if `β` is a normed space, then we show that the space of bounded
continuous functions from `α` to `β` inherits a normed space structure, by using
pointwise operations and checking that they are compatible with the uniform distance. -/


variable {𝕜 : Type*}
variable [TopologicalSpace α] [SeminormedAddCommGroup β]
variable {f g : α →ᵇ β} {x : α} {C : ℝ}

instance instNormedSpace [NormedField 𝕜] [NormedSpace 𝕜 β] : NormedSpace 𝕜 (α →ᵇ β) :=
  ⟨fun c f => by
    refine' norm_ofNormedAddCommGroup_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) _
    exact fun x =>
      norm_smul c (f x) ▸ mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) (norm_nonneg _)⟩

variable [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 β]
variable [SeminormedAddCommGroup γ] [NormedSpace 𝕜 γ]
variable (α)

-- TODO does this work in the `BoundedSMul` setting, too?
/-- Postcomposition of bounded continuous functions into a normed module by a continuous linear map
is a continuous linear map.
Upgraded version of `ContinuousLinearMap.compLeftContinuous`, similar to `LinearMap.compLeft`. -/
protected def _root_.ContinuousLinearMap.compLeftContinuousBounded (g : β →L[𝕜] γ) :
    (α →ᵇ β) →L[𝕜] α →ᵇ γ :=
  LinearMap.mkContinuous
    { toFun := fun f =>
        ofNormedAddCommGroup (g ∘ f) (g.continuous.comp f.continuous) (‖g‖ * ‖f‖) fun x =>
          g.le_opNorm_of_le (f.norm_coe_le_norm x)
      map_add' := fun f g => by ext; simp
      map_smul' := fun c f => by ext; simp } ‖g‖ fun f =>
        norm_ofNormedAddCommGroup_le _ (mul_nonneg (norm_nonneg g) (norm_nonneg f))
          (fun x => by exact g.le_opNorm_of_le (f.norm_coe_le_norm x))
#align continuous_linear_map.comp_left_continuous_bounded ContinuousLinearMap.compLeftContinuousBounded

structure

In this section, if `R` is a normed ring, then we show that the space of bounded
continuous functions from `α` to `R` inherits a normed ring structure, by using
pointwise operations and checking that they are compatible with the uniform distance. -/


variable [TopologicalSpace α] {R : Type*}

section NonUnital

section Seminormed

variable [NonUnitalSeminormedRing R]

instance instMul : Mul (α →ᵇ R) where
  mul f g :=
    ofNormedAddCommGroup (f * g) (f.continuous.mul g.continuous) (‖f‖ * ‖g‖) fun x =>
      le_trans (norm_mul_le (f x) (g x)) <|
        mul_le_mul (f.norm_coe_le_norm x) (g.norm_coe_le_norm x) (norm_nonneg _) (norm_nonneg _)

@[simp]
theorem coe_mul (f g : α →ᵇ R) : ⇑(f * g) = f * g := rfl
#align bounded_continuous_function.coe_mul BoundedContinuousFunction.coe_mul

structure

In this section, if `R` is a normed commutative ring, then we show that the space of bounded
continuous functions from `α` to `R` inherits a normed commutative ring structure, by using
pointwise operations and checking that they are compatible with the uniform distance. -/


variable [TopologicalSpace α] {R : Type*}

instance instCommRing [SeminormedCommRing R] : CommRing (α →ᵇ R) where
  mul_comm _ _ := ext fun _ ↦ mul_comm _ _

instance instSeminormedCommRing [SeminormedCommRing R] : SeminormedCommRing (α →ᵇ R) where
  __ := instCommRing
  __ := instSeminormedAddCommGroup
  -- Porting note (#10888): Added proof for `norm_mul`

structure

In this section, if `γ` is a normed algebra, then we show that the space of bounded
continuous functions from `α` to `γ` inherits a normed algebra structure, by using
pointwise operations and checking that they are compatible with the uniform distance. -/


variable {𝕜 : Type*} [NormedField 𝕜]
variable [TopologicalSpace α] [SeminormedAddCommGroup β] [NormedSpace 𝕜 β]
variable [NormedRing γ] [NormedAlgebra 𝕜 γ]
variable {f g : α →ᵇ γ} {x : α} {c : 𝕜}

/-- `BoundedContinuousFunction.const` as a `RingHom`. -/
def C : 𝕜 →+* α →ᵇ γ where
  toFun := fun c : 𝕜 => const α ((algebraMap 𝕜 γ) c)
  map_one' := ext fun _ => (algebraMap 𝕜 γ).map_one
  map_mul' _ _ := ext fun _ => (algebraMap 𝕜 γ).map_mul _ _
  map_zero' := ext fun _ => (algebraMap 𝕜 γ).map_zero
  map_add' _ _ := ext fun _ => (algebraMap 𝕜 γ).map_add _ _
set_option linter.uppercaseLean3 false in
#align bounded_continuous_function.C BoundedContinuousFunction.C