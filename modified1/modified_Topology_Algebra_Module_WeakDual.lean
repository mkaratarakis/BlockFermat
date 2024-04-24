def WeakBilin [CommSemiring 𝕜] [AddCommMonoid E] [Module 𝕜 E] [AddCommMonoid F] [Module 𝕜 F]
    (_ : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) := E
#align weak_bilin WeakBilin

def topDualPairing (𝕜 E) [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜] [AddCommMonoid E]
    [Module 𝕜 E] [TopologicalSpace E] [ContinuousConstSMul 𝕜 𝕜] : (E →L[𝕜] 𝕜) →ₗ[𝕜] E →ₗ[𝕜] 𝕜 :=
  ContinuousLinearMap.coeLM 𝕜
#align top_dual_pairing topDualPairing

def WeakDual (𝕜 E : Type*) [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
    [ContinuousConstSMul 𝕜 𝕜] [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E] :=
  WeakBilin (topDualPairing 𝕜 E)
#align weak_dual WeakDual

def WeakSpace (𝕜 E) [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
    [ContinuousConstSMul 𝕜 𝕜] [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E] :=
  WeakBilin (topDualPairing 𝕜 E).flip
#align weak_space WeakSpace

def map (f : E →L[𝕜] F) : WeakSpace 𝕜 E →L[𝕜] WeakSpace 𝕜 F :=
  { f with
    cont :=
      WeakBilin.continuous_of_continuous_eval _ fun l => WeakBilin.eval_continuous _ (l ∘L f) }
#align weak_space.map WeakSpace.map

def toWeakSpace : E ≃ₗ[𝕜] WeakSpace 𝕜 E := LinearEquiv.refl 𝕜 E

variable (𝕜 E) in
/-- For a topological vector space `E`, "identity mapping" `E → WeakSpace 𝕜 E` is continuous.
This definition implements it as a continuous linear map. -/
def continuousLinearMapToWeakSpace : E →L[𝕜] WeakSpace 𝕜 E where
  __ := toWeakSpace 𝕜 E
  cont := by
    apply WeakBilin.continuous_of_continuous_eval
    exact ContinuousLinearMap.continuous

variable (𝕜 E) in
@[simp]
theorem continuousLinearMapToWeakSpace_eq_toWeakSpace (x : E) :
    continuousLinearMapToWeakSpace 𝕜 E x = toWeakSpace 𝕜 E x := by rfl

theorem continuousLinearMapToWeakSpace_bijective :
    Function.Bijective (continuousLinearMapToWeakSpace 𝕜 E) :=
  (toWeakSpace 𝕜 E).bijective

/-- The canonical map from `WeakSpace 𝕜 E` to `E` is an open map. -/
theorem isOpenMap_toWeakSpace_symm : IsOpenMap (toWeakSpace 𝕜 E).symm :=
  IsOpenMap.of_inverse (continuousLinearMapToWeakSpace 𝕜 E).cont
    (toWeakSpace 𝕜 E).left_inv (toWeakSpace 𝕜 E).right_inv

/-- A set in `E` which is open in the weak topology is open. -/
theorem WeakSpace.isOpen_of_isOpen (V : Set E)
    (hV : IsOpen ((continuousLinearMapToWeakSpace 𝕜 E) '' V : Set (WeakSpace 𝕜 E))) : IsOpen V := by
  simpa [Set.image_image] using isOpenMap_toWeakSpace_symm _ hV

theorem tendsto_iff_forall_eval_tendsto_topDualPairing {l : Filter α} {f : α → WeakDual 𝕜 E}
    {x : WeakDual 𝕜 E} :
    Tendsto f l (𝓝 x) ↔
      ∀ y, Tendsto (fun i => topDualPairing 𝕜 E (f i) y) l (𝓝 (topDualPairing 𝕜 E x y)) :=
  WeakBilin.tendsto_iff_forall_eval_tendsto _ ContinuousLinearMap.coe_injective
#align tendsto_iff_forall_eval_tendsto_top_dual_pairing tendsto_iff_forall_eval_tendsto_topDualPairing