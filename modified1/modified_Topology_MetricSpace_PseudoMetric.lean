def UniformSpace.ofDist (dist : α → α → ℝ) (dist_self : ∀ x : α, dist x x = 0)
    (dist_comm : ∀ x y : α, dist x y = dist y x)
    (dist_triangle : ∀ x y z : α, dist x z ≤ dist x y + dist y z) : UniformSpace α :=
  .ofFun dist dist_self dist_comm dist_triangle ofDist_aux
#align uniform_space_of_dist UniformSpace.ofDist

def Bornology.ofDist {α : Type*} (dist : α → α → ℝ) (dist_comm : ∀ x y, dist x y = dist y x)
    (dist_triangle : ∀ x y z, dist x z ≤ dist x y + dist y z) : Bornology α :=
  Bornology.ofBounded { s : Set α | ∃ C, ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → dist x y ≤ C }
    ⟨0, fun x hx y => hx.elim⟩ (fun s ⟨c, hc⟩ t h => ⟨c, fun x hx y hy => hc (h hx) (h hy)⟩)
    (fun s hs t ht => by
      rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
      · rwa [empty_union]
      rcases t.eq_empty_or_nonempty with rfl | ⟨y, hy⟩
      · rwa [union_empty]
      rsuffices ⟨C, hC⟩ : ∃ C, ∀ z ∈ s ∪ t, dist x z ≤ C
      · refine ⟨C + C, fun a ha b hb => (dist_triangle a x b).trans ?_⟩
        simpa only [dist_comm] using add_le_add (hC _ ha) (hC _ hb)
      rcases hs with ⟨Cs, hs⟩; rcases ht with ⟨Ct, ht⟩
      refine ⟨max Cs (dist x y + Ct), fun z hz => hz.elim
        (fun hz => (hs hx hz).trans (le_max_left _ _))
        (fun hz => (dist_triangle x y z).trans <|
          (add_le_add le_rfl (ht hy hz)).trans (le_max_right _ _))⟩)
    fun z => ⟨dist z z, forall_eq.2 <| forall_eq.2 le_rfl⟩
#align bornology.of_dist Bornology.ofDistₓ

def PseudoMetricSpace.ofDistTopology {α : Type u} [TopologicalSpace α] (dist : α → α → ℝ)
    (dist_self : ∀ x : α, dist x x = 0) (dist_comm : ∀ x y : α, dist x y = dist y x)
    (dist_triangle : ∀ x y z : α, dist x z ≤ dist x y + dist y z)
    (H : ∀ s : Set α, IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, ∀ y, dist x y < ε → y ∈ s) :
    PseudoMetricSpace α :=
  { dist := dist
    dist_self := dist_self
    dist_comm := dist_comm
    dist_triangle := dist_triangle
    edist_dist := fun x y => by exact ENNReal.coe_nnreal_eq _
    toUniformSpace :=
      (UniformSpace.ofDist dist dist_self dist_comm dist_triangle).replaceTopology <|
        TopologicalSpace.ext_iff.2 fun s ↦ (H s).trans <| forall₂_congr fun x _ ↦
          ((UniformSpace.hasBasis_ofFun (exists_gt (0 : ℝ)) dist dist_self dist_comm dist_triangle
            UniformSpace.ofDist_aux).comap (Prod.mk x)).mem_iff.symm
    uniformity_dist := rfl
    toBornology := Bornology.ofDist dist dist_comm dist_triangle
    cobounded_sets := rfl }
#align pseudo_metric_space.of_dist_topology PseudoMetricSpace.ofDistTopology

def evalDist : PositivityExt where eval {u α} _zα _pα e := do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@Dist.dist $β $inst $a $b) =>
    let _inst ← synthInstanceQ q(PseudoMetricSpace $β)
    assertInstancesCommute
    pure (.nonnegative q(dist_nonneg))
  | _, _, _ => throwError "not dist"

end Mathlib.Meta.Positivity

example {x y : α} : 0 ≤ dist x y := by positivity

@[simp] theorem abs_dist {a b : α} : |dist a b| = dist a b := abs_of_nonneg dist_nonneg
#align abs_dist abs_dist

def ball (x : α) (ε : ℝ) : Set α :=
  { y | dist y x < ε }
#align metric.ball Metric.ball

def closedBall (x : α) (ε : ℝ) :=
  { y | dist y x ≤ ε }
#align metric.closed_ball Metric.closedBall

def sphere (x : α) (ε : ℝ) := { y | dist y x = ε }
#align metric.sphere Metric.sphere

def PseudoMetricSpace.replaceUniformity {α} [U : UniformSpace α] (m : PseudoMetricSpace α)
    (H : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace]) : PseudoMetricSpace α :=
  { m with
    toUniformSpace := U
    uniformity_dist := H.trans PseudoMetricSpace.uniformity_dist }
#align pseudo_metric_space.replace_uniformity PseudoMetricSpace.replaceUniformity

def PseudoMetricSpace.replaceTopology {γ} [U : TopologicalSpace γ] (m : PseudoMetricSpace γ)
    (H : U = m.toUniformSpace.toTopologicalSpace) : PseudoMetricSpace γ :=
  @PseudoMetricSpace.replaceUniformity γ (m.toUniformSpace.replaceTopology H) m rfl
#align pseudo_metric_space.replace_topology PseudoMetricSpace.replaceTopology

def PseudoEMetricSpace.toPseudoMetricSpaceOfDist {α : Type u} [e : PseudoEMetricSpace α]
    (dist : α → α → ℝ) (edist_ne_top : ∀ x y : α, edist x y ≠ ⊤)
    (h : ∀ x y, dist x y = ENNReal.toReal (edist x y)) : PseudoMetricSpace α where
  dist := dist
  dist_self x := by simp [h]
  dist_comm x y := by simp [h, edist_comm]
  dist_triangle x y z := by
    simp only [h]
    exact ENNReal.toReal_le_add (edist_triangle _ _ _) (edist_ne_top _ _) (edist_ne_top _ _)
  edist := edist
  edist_dist _ _ := by simp only [h, ENNReal.ofReal_toReal (edist_ne_top _ _)]
  toUniformSpace := e.toUniformSpace
  uniformity_dist := e.uniformity_edist.trans <| by
    simpa only [ENNReal.coe_toNNReal (edist_ne_top _ _), h]
      using (Metric.uniformity_edist_aux fun x y : α => (edist x y).toNNReal).symm
#align pseudo_emetric_space.to_pseudo_metric_space_of_dist PseudoEMetricSpace.toPseudoMetricSpaceOfDist

def PseudoEMetricSpace.toPseudoMetricSpace {α : Type u} [PseudoEMetricSpace α]
    (h : ∀ x y : α, edist x y ≠ ⊤) : PseudoMetricSpace α :=
  PseudoEMetricSpace.toPseudoMetricSpaceOfDist (fun x y => ENNReal.toReal (edist x y)) h fun _ _ =>
    rfl
#align pseudo_emetric_space.to_pseudo_metric_space PseudoEMetricSpace.toPseudoMetricSpace

def PseudoMetricSpace.replaceBornology {α} [B : Bornology α] (m : PseudoMetricSpace α)
    (H : ∀ s, @IsBounded _ B s ↔ @IsBounded _ PseudoMetricSpace.toBornology s) :
    PseudoMetricSpace α :=
  { m with
    toBornology := B
    cobounded_sets := Set.ext <| compl_surjective.forall.2 fun s =>
        (H s).trans <| by rw [isBounded_iff, mem_setOf_eq, compl_compl] }
#align pseudo_metric_space.replace_bornology PseudoMetricSpace.replaceBornology

def PseudoMetricSpace.induced {α β} (f : α → β) (m : PseudoMetricSpace β) :
    PseudoMetricSpace α where
  dist x y := dist (f x) (f y)
  dist_self x := dist_self _
  dist_comm x y := dist_comm _ _
  dist_triangle x y z := dist_triangle _ _ _
  edist x y := edist (f x) (f y)
  edist_dist x y := edist_dist _ _
  toUniformSpace := UniformSpace.comap f m.toUniformSpace
  uniformity_dist := (uniformity_basis_dist.comap _).eq_biInf
  toBornology := Bornology.induced f
  cobounded_sets := Set.ext fun s => mem_comap_iff_compl.trans <| by
    simp only [← isBounded_def, isBounded_iff, forall_mem_image, mem_setOf]
#align pseudo_metric_space.induced PseudoMetricSpace.induced

def Inducing.comapPseudoMetricSpace {α β} [TopologicalSpace α] [m : PseudoMetricSpace β] {f : α → β}
    (hf : Inducing f) : PseudoMetricSpace α :=
  .replaceTopology (.induced f m) hf.induced
#align inducing.comap_pseudo_metric_space Inducing.comapPseudoMetricSpace

def UniformInducing.comapPseudoMetricSpace {α β} [UniformSpace α] [m : PseudoMetricSpace β]
    (f : α → β) (h : UniformInducing f) : PseudoMetricSpace α :=
  .replaceUniformity (.induced f m) h.comap_uniformity.symm
#align uniform_inducing.comap_pseudo_metric_space UniformInducing.comapPseudoMetricSpace

def (f g : ∀ b, π b) : nndist f g = sup univ fun b => nndist (f b) (g b) :=
  NNReal.eq rfl
#align nndist_pi_def nndist_pi_def

def (f g : ∀ b, π b) : dist f g = (sup univ fun b => nndist (f b) (g b) : ℝ≥0) :=
  rfl
#align dist_pi_def dist_pi_def

structure from a distance function and metric space axioms -/
def UniformSpace.ofDist (dist : α → α → ℝ) (dist_self : ∀ x : α, dist x x = 0)
    (dist_comm : ∀ x y : α, dist x y = dist y x)
    (dist_triangle : ∀ x y z : α, dist x z ≤ dist x y + dist y z) : UniformSpace α :=
  .ofFun dist dist_self dist_comm dist_triangle ofDist_aux
#align uniform_space_of_dist UniformSpace.ofDist

structure and the emetric space structure are embedded in the metric space structure
-- to avoid instance diamond issues. See Note [forgetful inheritance].
/-- This is an internal lemma used inside the default of `PseudoMetricSpace.edist`. -/
private theorem dist_nonneg' {α} {x y : α} (dist : α → α → ℝ)
    (dist_self : ∀ x : α, dist x x = 0) (dist_comm : ∀ x y : α, dist x y = dist y x)
    (dist_triangle : ∀ x y z : α, dist x z ≤ dist x y + dist y z) : 0 ≤ dist x y :=
  have : 0 ≤ 2 * dist x y :=
    calc 0 = dist x x := (dist_self _).symm
    _ ≤ dist x y + dist y x := dist_triangle _ _ _
    _ = 2 * dist x y := by rw [two_mul, dist_comm]
  nonneg_of_mul_nonneg_right this two_pos

#noalign pseudo_metric_space.edist_dist_tac -- Porting note (#11215): TODO: restore

structure whose underlying topological space structure
(definitionally) agrees which a pre-existing topology which is compatible with a given distance
function. -/
def PseudoMetricSpace.ofDistTopology {α : Type u} [TopologicalSpace α] (dist : α → α → ℝ)
    (dist_self : ∀ x : α, dist x x = 0) (dist_comm : ∀ x y : α, dist x y = dist y x)
    (dist_triangle : ∀ x y z : α, dist x z ≤ dist x y + dist y z)
    (H : ∀ s : Set α, IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, ∀ y, dist x y < ε → y ∈ s) :
    PseudoMetricSpace α :=
  { dist := dist
    dist_self := dist_self
    dist_comm := dist_comm
    dist_triangle := dist_triangle
    edist_dist := fun x y => by exact ENNReal.coe_nnreal_eq _
    toUniformSpace :=
      (UniformSpace.ofDist dist dist_self dist_comm dist_triangle).replaceTopology <|
        TopologicalSpace.ext_iff.2 fun s ↦ (H s).trans <| forall₂_congr fun x _ ↦
          ((UniformSpace.hasBasis_ofFun (exists_gt (0 : ℝ)) dist dist_self dist_comm dist_triangle
            UniformSpace.ofDist_aux).comap (Prod.mk x)).mem_iff.symm
    uniformity_dist := rfl
    toBornology := Bornology.ofDist dist dist_comm dist_triangle
    cobounded_sets := rfl }
#align pseudo_metric_space.of_dist_topology PseudoMetricSpace.ofDistTopology

structure coming from the edistance and the
distance coincide. -/

-- Porting note (#10756): new theorem

structure is provably
(but typically non-definitionaly) equal to some given uniform structure.
See Note [forgetful inheritance].
-/
@[reducible]
def PseudoMetricSpace.replaceUniformity {α} [U : UniformSpace α] (m : PseudoMetricSpace α)
    (H : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace]) : PseudoMetricSpace α :=
  { m with
    toUniformSpace := U
    uniformity_dist := H.trans PseudoMetricSpace.uniformity_dist }
#align pseudo_metric_space.replace_uniformity PseudoMetricSpace.replaceUniformity

structure is
provably (but typically non-definitionaly) equal to some given topological structure.
See Note [forgetful inheritance].
-/
@[reducible]
def PseudoMetricSpace.replaceTopology {γ} [U : TopologicalSpace γ] (m : PseudoMetricSpace γ)
    (H : U = m.toUniformSpace.toTopologicalSpace) : PseudoMetricSpace γ :=
  @PseudoMetricSpace.replaceUniformity γ (m.toUniformSpace.replaceTopology H) m rfl
#align pseudo_metric_space.replace_topology PseudoMetricSpace.replaceTopology

structure is provably
(but typically non-definitionaly) equal to some given bornology structure.
See Note [forgetful inheritance].
-/
@[reducible]
def PseudoMetricSpace.replaceBornology {α} [B : Bornology α] (m : PseudoMetricSpace α)
    (H : ∀ s, @IsBounded _ B s ↔ @IsBounded _ PseudoMetricSpace.toBornology s) :
    PseudoMetricSpace α :=
  { m with
    toBornology := B
    cobounded_sets := Set.ext <| compl_surjective.forall.2 fun s =>
        (H s).trans <| by rw [isBounded_iff, mem_setOf_eq, compl_compl] }
#align pseudo_metric_space.replace_bornology PseudoMetricSpace.replaceBornology

structure pulled back by a function. -/
@[reducible]
def PseudoMetricSpace.induced {α β} (f : α → β) (m : PseudoMetricSpace β) :
    PseudoMetricSpace α where
  dist x y := dist (f x) (f y)
  dist_self x := dist_self _
  dist_comm x y := dist_comm _ _
  dist_triangle x y z := dist_triangle _ _ _
  edist x y := edist (f x) (f y)
  edist_dist x y := edist_dist _ _
  toUniformSpace := UniformSpace.comap f m.toUniformSpace
  uniformity_dist := (uniformity_basis_dist.comap _).eq_biInf
  toBornology := Bornology.induced f
  cobounded_sets := Set.ext fun s => mem_comap_iff_compl.trans <| by
    simp only [← isBounded_def, isBounded_iff, forall_mem_image, mem_setOf]
#align pseudo_metric_space.induced PseudoMetricSpace.induced

structure by an inducing map. This is a version of
`PseudoMetricSpace.induced` useful in case if the domain already has a `TopologicalSpace`
structure. -/
def Inducing.comapPseudoMetricSpace {α β} [TopologicalSpace α] [m : PseudoMetricSpace β] {f : α → β}
    (hf : Inducing f) : PseudoMetricSpace α :=
  .replaceTopology (.induced f m) hf.induced
#align inducing.comap_pseudo_metric_space Inducing.comapPseudoMetricSpace

structure by a uniform inducing map. This is a version of
`PseudoMetricSpace.induced` useful in case if the domain already has a `UniformSpace`
structure. -/
def UniformInducing.comapPseudoMetricSpace {α β} [UniformSpace α] [m : PseudoMetricSpace β]
    (f : α → β) (h : UniformInducing f) : PseudoMetricSpace α :=
  .replaceUniformity (.induced f m) h.comap_uniformity.symm
#align uniform_inducing.comap_pseudo_metric_space UniformInducing.comapPseudoMetricSpace