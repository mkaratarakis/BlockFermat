def coeRingHom : α →+* Completion α where
  toFun := (↑)
  map_one' := coe_one α
  map_zero' := coe_zero
  map_add' := coe_add
  map_mul' := coe_mul
#align uniform_space.completion.coe_ring_hom UniformSpace.Completion.coeRingHom

def extensionHom [CompleteSpace β] [T0Space β] : Completion α →+* β :=
  have hf' : Continuous (f : α →+ β) := hf
  -- helping the elaborator
  have hf : UniformContinuous f := uniformContinuous_addMonoidHom_of_continuous hf'
  { toFun := Completion.extension f
    map_zero' := by simp_rw [← coe_zero, extension_coe hf, f.map_zero]
    map_add' := fun a b =>
      Completion.induction_on₂ a b
        (isClosed_eq (continuous_extension.comp continuous_add)
          ((continuous_extension.comp continuous_fst).add
            (continuous_extension.comp continuous_snd)))
        fun a b => by
        simp_rw [← coe_add, extension_coe hf, f.map_add]
    map_one' := by rw [← coe_one, extension_coe hf, f.map_one]
    map_mul' := fun a b =>
      Completion.induction_on₂ a b
        (isClosed_eq (continuous_extension.comp continuous_mul)
          ((continuous_extension.comp continuous_fst).mul
            (continuous_extension.comp continuous_snd)))
        fun a b => by
        simp_rw [← coe_mul, extension_coe hf, f.map_mul] }
#align uniform_space.completion.extension_hom UniformSpace.Completion.extensionHom

def mapRingHom (hf : Continuous f) : Completion α →+* Completion β :=
  extensionHom (coeRingHom.comp f) (continuous_coeRingHom.comp hf)
#align uniform_space.completion.map_ring_hom UniformSpace.Completion.mapRingHom

def (r : R) :
    algebraMap R (Completion A) r = (algebraMap R A r : Completion A) :=
  rfl
#align uniform_space.completion.algebra_map_def UniformSpace.Completion.algebraMap_def

def _).symm
#align uniform_space.ring_sep_rel UniformSpace.inseparableSetoid_ring

def sepQuotHomeomorphRingQuot (α) [CommRing α] [TopologicalSpace α] [TopologicalRing α] :
    SeparationQuotient α ≃ₜ α ⧸ (⊥ : Ideal α).closure where
  toEquiv := Quotient.congrRight fun x y => by rw [inseparableSetoid_ring]
  continuous_toFun := continuous_id.quotient_map' <| by
    rw [inseparableSetoid_ring]; exact fun _ _ ↦ id
  continuous_invFun := continuous_id.quotient_map' <| by
    rw [inseparableSetoid_ring]; exact fun _ _ ↦ id
#align uniform_space.sep_quot_equiv_ring_quot UniformSpace.sepQuotHomeomorphRingQuot

def sepQuotRingEquivRingQuot (α) [CommRing α] [TopologicalSpace α] [TopologicalRing α] :
    SeparationQuotient α ≃+* α ⧸ (⊥ : Ideal α).closure :=
  (sepQuotHomeomorphRingQuot _).ringEquiv

instance topologicalRing [CommRing α] [TopologicalSpace α] [TopologicalRing α] :
    TopologicalRing (SeparationQuotient α) where
  toContinuousAdd :=
    Inducing.continuousAdd (sepQuotRingEquivRingQuot α) (sepQuotHomeomorphRingQuot α).inducing
  toContinuousMul :=
    Inducing.continuousMul (sepQuotRingEquivRingQuot α) (sepQuotHomeomorphRingQuot α).inducing
  toContinuousNeg :=
    Inducing.continuousNeg (sepQuotHomeomorphRingQuot α).inducing <|
      map_neg (sepQuotRingEquivRingQuot α)
#align uniform_space.topological_ring UniformSpace.topologicalRing

def DenseInducing.extendRingHom {i : α →+* β} {f : α →+* γ} (ue : UniformInducing i)
    (dr : DenseRange i) (hf : UniformContinuous f) : β →+* γ where
  toFun := (ue.denseInducing dr).extend f
  map_one' := by
    convert DenseInducing.extend_eq (ue.denseInducing dr) hf.continuous 1
    exacts [i.map_one.symm, f.map_one.symm]
  map_zero' := by
    convert DenseInducing.extend_eq (ue.denseInducing dr) hf.continuous 0 <;>
    simp only [map_zero]
  map_add' := by
    have h := (uniformContinuous_uniformly_extend ue dr hf).continuous
    refine' fun x y => DenseRange.induction_on₂ dr _ (fun a b => _) x y
    · exact isClosed_eq (Continuous.comp h continuous_add)
        ((h.comp continuous_fst).add (h.comp continuous_snd))
    · simp_rw [← i.map_add, DenseInducing.extend_eq (ue.denseInducing dr) hf.continuous _,
        ← f.map_add]
  map_mul' := by
    have h := (uniformContinuous_uniformly_extend ue dr hf).continuous
    refine' fun x y => DenseRange.induction_on₂ dr _ (fun a b => _) x y
    · exact isClosed_eq (Continuous.comp h continuous_mul)
        ((h.comp continuous_fst).mul (h.comp continuous_snd))
    · simp_rw [← i.map_mul, DenseInducing.extend_eq (ue.denseInducing dr) hf.continuous _,
        ← f.map_mul]
#align dense_inducing.extend_ring_hom DenseInducing.extendRingHom

structure
on the completion of a ring endowed with a compatible uniform structure in the sense of
`UniformAddGroup`. There is also a commutative version when the original ring is commutative.
Moreover, if a topological ring is an algebra over a commutative semiring, then so is its
`UniformSpace.Completion`.

The last part of the file builds a ring structure on the biggest separated quotient of a ring.

## Main declarations:

structure that makes subtraction uniformly
continuous, get an homeomorphism between the separated quotient of `α` and the quotient ring
corresponding to the closure of zero. -/
def sepQuotHomeomorphRingQuot (α) [CommRing α] [TopologicalSpace α] [TopologicalRing α] :
    SeparationQuotient α ≃ₜ α ⧸ (⊥ : Ideal α).closure where
  toEquiv := Quotient.congrRight fun x y => by rw [inseparableSetoid_ring]
  continuous_toFun := continuous_id.quotient_map' <| by
    rw [inseparableSetoid_ring]; exact fun _ _ ↦ id
  continuous_invFun := continuous_id.quotient_map' <| by
    rw [inseparableSetoid_ring]; exact fun _ _ ↦ id
#align uniform_space.sep_quot_equiv_ring_quot UniformSpace.sepQuotHomeomorphRingQuot

structure that makes subtraction uniformly
continuous, get an equivalence between the separated quotient of `α` and the quotient ring
corresponding to the closure of zero. -/
def sepQuotRingEquivRingQuot (α) [CommRing α] [TopologicalSpace α] [TopologicalRing α] :
    SeparationQuotient α ≃+* α ⧸ (⊥ : Ideal α).closure :=
  (sepQuotHomeomorphRingQuot _).ringEquiv

instance topologicalRing [CommRing α] [TopologicalSpace α] [TopologicalRing α] :
    TopologicalRing (SeparationQuotient α) where
  toContinuousAdd :=
    Inducing.continuousAdd (sepQuotRingEquivRingQuot α) (sepQuotHomeomorphRingQuot α).inducing
  toContinuousMul :=
    Inducing.continuousMul (sepQuotRingEquivRingQuot α) (sepQuotHomeomorphRingQuot α).inducing
  toContinuousNeg :=
    Inducing.continuousNeg (sepQuotHomeomorphRingQuot α).inducing <|
      map_neg (sepQuotRingEquivRingQuot α)
#align uniform_space.topological_ring UniformSpace.topologicalRing