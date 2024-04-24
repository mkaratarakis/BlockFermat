def uniformSpaceOfEDist (edist : α → α → ℝ≥0∞) (edist_self : ∀ x : α, edist x x = 0)
    (edist_comm : ∀ x y : α, edist x y = edist y x)
    (edist_triangle : ∀ x y z : α, edist x z ≤ edist x y + edist y z) : UniformSpace α :=
  .ofFun edist edist_self edist_comm edist_triangle fun ε ε0 =>
    ⟨ε / 2, ENNReal.half_pos ε0.ne', fun _ h₁ _ h₂ =>
      (ENNReal.add_lt_add h₁ h₂).trans_eq (ENNReal.add_halves _)⟩
#align uniform_space_of_edist uniformSpaceOfEDist

def PseudoEMetricSpace.replaceUniformity {α} [U : UniformSpace α] (m : PseudoEMetricSpace α)
    (H : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace]) : PseudoEMetricSpace α where
  edist := @edist _ m.toEDist
  edist_self := edist_self
  edist_comm := edist_comm
  edist_triangle := edist_triangle
  toUniformSpace := U
  uniformity_edist := H.trans (@PseudoEMetricSpace.uniformity_edist α _)
#align pseudo_emetric_space.replace_uniformity PseudoEMetricSpace.replaceUniformity

def PseudoEMetricSpace.induced {α β} (f : α → β) (m : PseudoEMetricSpace β) :
    PseudoEMetricSpace α where
  edist x y := edist (f x) (f y)
  edist_self _ := edist_self _
  edist_comm _ _ := edist_comm _ _
  edist_triangle _ _ _ := edist_triangle _ _ _
  toUniformSpace := UniformSpace.comap f m.toUniformSpace
  uniformity_edist := (uniformity_basis_edist.comap (Prod.map f f)).eq_biInf
#align pseudo_emetric_space.induced PseudoEMetricSpace.induced

def [∀ b, EDist (π b)] (f g : ∀ b, π b) :
    edist f g = Finset.sup univ fun b => edist (f b) (g b) :=
  rfl
#align edist_pi_def edist_pi_def

def ball (x : α) (ε : ℝ≥0∞) : Set α :=
  { y | edist y x < ε }
#align emetric.ball EMetric.ball

def closedBall (x : α) (ε : ℝ≥0∞) :=
  { y | edist y x ≤ ε }
#align emetric.closed_ball EMetric.closedBall

def edistLtTopSetoid : Setoid α where
  r x y := edist x y < ⊤
  iseqv :=
    ⟨fun x => by rw [edist_self]; exact ENNReal.coe_lt_top,
      fun h => by rwa [edist_comm], fun hxy hyz =>
        lt_of_le_of_lt (edist_triangle _ _ _) (ENNReal.add_lt_top.2 ⟨hxy, hyz⟩)⟩
#align emetric.edist_lt_top_setoid EMetric.edistLtTopSetoid

def diam (s : Set α) :=
  ⨆ (x ∈ s) (y ∈ s), edist x y
#align emetric.diam EMetric.diam

def EMetricSpace.ofT0PseudoEMetricSpace (α : Type*) [PseudoEMetricSpace α] [T0Space α] :
    EMetricSpace α :=
  { ‹PseudoEMetricSpace α› with
    eq_of_edist_eq_zero := fun h => (EMetric.inseparable_iff.2 h).eq }
#align emetric_space.of_t0_pseudo_emetric_space EMetricSpace.ofT0PseudoEMetricSpace

def EMetricSpace.replaceUniformity {γ} [U : UniformSpace γ] (m : EMetricSpace γ)
    (H : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace]) : EMetricSpace γ where
  edist := @edist _ m.toEDist
  edist_self := edist_self
  eq_of_edist_eq_zero := @eq_of_edist_eq_zero _ _
  edist_comm := edist_comm
  edist_triangle := edist_triangle
  toUniformSpace := U
  uniformity_edist := H.trans (@PseudoEMetricSpace.uniformity_edist γ _)
#align emetric_space.replace_uniformity EMetricSpace.replaceUniformity

def EMetricSpace.induced {γ β} (f : γ → β) (hf : Function.Injective f) (m : EMetricSpace β) :
    EMetricSpace γ :=
  { PseudoEMetricSpace.induced f m.toPseudoEMetricSpace with
    eq_of_edist_eq_zero := fun h => hf (edist_eq_zero.1 h) }
#align emetric_space.induced EMetricSpace.induced

structure is embedded in the emetric space structure
-- to avoid instance diamond issues. See Note [forgetful inheritance].
/-- Extended (pseudo) metric spaces, with an extended distance `edist` possibly taking the
value ∞

Each pseudo_emetric space induces a canonical `UniformSpace` and hence a canonical
`TopologicalSpace`.
This is enforced in the type class definition, by extending the `UniformSpace` structure. When
instantiating a `PseudoEMetricSpace` structure, the uniformity fields are not necessary, they
will be filled in by default. There is a default value for the uniformity, that can be substituted
in cases of interest, for instance when instantiating a `PseudoEMetricSpace` structure
on a product.

Continuity of `edist` is proved in `Topology.Instances.ENNReal`
-/
class PseudoEMetricSpace (α : Type u) extends EDist α : Type u where
  edist_self : ∀ x : α, edist x x = 0
  edist_comm : ∀ x y : α, edist x y = edist y x
  edist_triangle : ∀ x y z : α, edist x z ≤ edist x y + edist y z
  toUniformSpace : UniformSpace α := uniformSpaceOfEDist edist edist_self edist_comm edist_triangle
  uniformity_edist : 𝓤 α = ⨅ ε > 0, 𝓟 { p : α × α | edist p.1 p.2 < ε } := by rfl
#align pseudo_emetric_space PseudoEMetricSpace

structure in terms of the extended distance -/
theorem uniformity_pseudoedist : 𝓤 α = ⨅ ε > 0, 𝓟 { p : α × α | edist p.1 p.2 < ε } :=
  PseudoEMetricSpace.uniformity_edist
#align uniformity_pseudoedist uniformity_pseudoedist

structure -/
theorem edist_mem_uniformity {ε : ℝ≥0∞} (ε0 : 0 < ε) : { p : α × α | edist p.1 p.2 < ε } ∈ 𝓤 α :=
  mem_uniformity_edist.2 ⟨ε, ε0, id⟩
#align edist_mem_uniformity edist_mem_uniformity

structure thus constructed is the one
corresponding to the product of uniform spaces, to avoid diamond problems. -/
instance Prod.pseudoEMetricSpaceMax [PseudoEMetricSpace β] : PseudoEMetricSpace (α × β) where
  edist x y := edist x.1 y.1 ⊔ edist x.2 y.2
  edist_self x := by simp
  edist_comm x y := by simp [edist_comm]
  edist_triangle x y z :=
    max_le (le_trans (edist_triangle _ _ _) (add_le_add (le_max_left _ _) (le_max_left _ _)))
      (le_trans (edist_triangle _ _ _) (add_le_add (le_max_right _ _) (le_max_right _ _)))
  uniformity_edist := uniformity_prod.trans <| by
    simp [PseudoEMetricSpace.uniformity_edist, ← iInf_inf_eq, setOf_and]
  toUniformSpace := inferInstance
#align prod.pseudo_emetric_space_max Prod.pseudoEMetricSpaceMax

structure thus constructed is the one
corresponding to the product of uniform spaces, to avoid diamond problems. -/
instance Prod.emetricSpaceMax [EMetricSpace β] : EMetricSpace (γ × β) :=
  .ofT0PseudoEMetricSpace _
#align prod.emetric_space_max Prod.emetricSpaceMax

structure in terms of the extended distance -/
theorem uniformity_edist : 𝓤 γ = ⨅ ε > 0, 𝓟 { p : γ × γ | edist p.1 p.2 < ε } :=
  PseudoEMetricSpace.uniformity_edist
#align uniformity_edist uniformity_edist