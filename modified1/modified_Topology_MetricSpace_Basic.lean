def MetricSpace.ofDistTopology {α : Type u} [TopologicalSpace α] (dist : α → α → ℝ)
    (dist_self : ∀ x : α, dist x x = 0) (dist_comm : ∀ x y : α, dist x y = dist y x)
    (dist_triangle : ∀ x y z : α, dist x z ≤ dist x y + dist y z)
    (H : ∀ s : Set α, IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, ∀ y, dist x y < ε → y ∈ s)
    (eq_of_dist_eq_zero : ∀ x y : α, dist x y = 0 → x = y) : MetricSpace α :=
  { PseudoMetricSpace.ofDistTopology dist dist_self dist_comm dist_triangle H with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero _ _ }
#align metric_space.of_dist_topology MetricSpace.ofDistTopology

def _root_.MetricSpace.ofT0PseudoMetricSpace (α : Type*) [PseudoMetricSpace α] [T0Space α] :
    MetricSpace α where
  toPseudoMetricSpace := ‹_›
  eq_of_dist_eq_zero hdist := (Metric.inseparable_iff.2 hdist).eq
#align metric_space.of_t0_pseudo_metric_space MetricSpace.ofT0PseudoMetricSpace

def MetricSpace.replaceUniformity {γ} [U : UniformSpace γ] (m : MetricSpace γ)
    (H : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace]) : MetricSpace γ where
  toPseudoMetricSpace := PseudoMetricSpace.replaceUniformity m.toPseudoMetricSpace H
  eq_of_dist_eq_zero := @eq_of_dist_eq_zero _ _
#align metric_space.replace_uniformity MetricSpace.replaceUniformity

def MetricSpace.replaceTopology {γ} [U : TopologicalSpace γ] (m : MetricSpace γ)
    (H : U = m.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace) : MetricSpace γ :=
  @MetricSpace.replaceUniformity γ (m.toUniformSpace.replaceTopology H) m rfl
#align metric_space.replace_topology MetricSpace.replaceTopology

def EMetricSpace.toMetricSpaceOfDist {α : Type u} [EMetricSpace α] (dist : α → α → ℝ)
    (edist_ne_top : ∀ x y : α, edist x y ≠ ⊤) (h : ∀ x y, dist x y = ENNReal.toReal (edist x y)) :
    MetricSpace α :=
  @MetricSpace.ofT0PseudoMetricSpace _
    (PseudoEMetricSpace.toPseudoMetricSpaceOfDist dist edist_ne_top h) _
#align emetric_space.to_metric_space_of_dist EMetricSpace.toMetricSpaceOfDist

def EMetricSpace.toMetricSpace {α : Type u} [EMetricSpace α] (h : ∀ x y : α, edist x y ≠ ⊤) :
    MetricSpace α :=
  EMetricSpace.toMetricSpaceOfDist (fun x y => ENNReal.toReal (edist x y)) h fun _ _ => rfl
#align emetric_space.to_metric_space EMetricSpace.toMetricSpace

def MetricSpace.replaceBornology {α} [B : Bornology α] (m : MetricSpace α)
    (H : ∀ s, @IsBounded _ B s ↔ @IsBounded _ PseudoMetricSpace.toBornology s) : MetricSpace α :=
  { PseudoMetricSpace.replaceBornology _ H, m with toBornology := B }
#align metric_space.replace_bornology MetricSpace.replaceBornology

def MetricSpace.induced {γ β} (f : γ → β) (hf : Function.Injective f) (m : MetricSpace β) :
    MetricSpace γ :=
  { PseudoMetricSpace.induced f m.toPseudoMetricSpace with
    eq_of_dist_eq_zero := fun h => hf (dist_eq_zero.1 h) }
#align metric_space.induced MetricSpace.induced

def UniformEmbedding.comapMetricSpace {α β} [UniformSpace α] [m : MetricSpace β] (f : α → β)
    (h : UniformEmbedding f) : MetricSpace α :=
  .replaceUniformity (.induced f h.inj m) h.comap_uniformity.symm
#align uniform_embedding.comap_metric_space UniformEmbedding.comapMetricSpace

def Embedding.comapMetricSpace {α β} [TopologicalSpace α] [m : MetricSpace β] (f : α → β)
    (h : Embedding f) : MetricSpace α :=
  .replaceTopology (.induced f h.inj m) h.induced
#align embedding.comap_metric_space Embedding.comapMetricSpace

structure whose underlying topological space structure
(definitionally) agrees which a pre-existing topology which is compatible with a given distance
function. -/
def MetricSpace.ofDistTopology {α : Type u} [TopologicalSpace α] (dist : α → α → ℝ)
    (dist_self : ∀ x : α, dist x x = 0) (dist_comm : ∀ x y : α, dist x y = dist y x)
    (dist_triangle : ∀ x y z : α, dist x z ≤ dist x y + dist y z)
    (H : ∀ s : Set α, IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, ∀ y, dist x y < ε → y ∈ s)
    (eq_of_dist_eq_zero : ∀ x y : α, dist x y = 0 → x = y) : MetricSpace α :=
  { PseudoMetricSpace.ofDistTopology dist dist_self dist_comm dist_triangle H with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero _ _ }
#align metric_space.of_dist_topology MetricSpace.ofDistTopology

structure is provably
(but typically non-definitionaly) equal to some given uniform structure.
See Note [forgetful inheritance].
-/
def MetricSpace.replaceUniformity {γ} [U : UniformSpace γ] (m : MetricSpace γ)
    (H : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace]) : MetricSpace γ where
  toPseudoMetricSpace := PseudoMetricSpace.replaceUniformity m.toPseudoMetricSpace H
  eq_of_dist_eq_zero := @eq_of_dist_eq_zero _ _
#align metric_space.replace_uniformity MetricSpace.replaceUniformity

structure is provably
(but typically non-definitionaly) equal to some given topological structure.
See Note [forgetful inheritance].
-/
@[reducible]
def MetricSpace.replaceTopology {γ} [U : TopologicalSpace γ] (m : MetricSpace γ)
    (H : U = m.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace) : MetricSpace γ :=
  @MetricSpace.replaceUniformity γ (m.toUniformSpace.replaceTopology H) m rfl
#align metric_space.replace_topology MetricSpace.replaceTopology

structure is provably
(but typically non-definitionaly) equal to some given bornology structure.
See Note [forgetful inheritance].
-/
def MetricSpace.replaceBornology {α} [B : Bornology α] (m : MetricSpace α)
    (H : ∀ s, @IsBounded _ B s ↔ @IsBounded _ PseudoMetricSpace.toBornology s) : MetricSpace α :=
  { PseudoMetricSpace.replaceBornology _ H, m with toBornology := B }
#align metric_space.replace_bornology MetricSpace.replaceBornology

structure pulled back by an injective function. Injectivity is necessary to
ensure that `dist x y = 0` only if `x = y`. -/
@[reducible]
def MetricSpace.induced {γ β} (f : γ → β) (hf : Function.Injective f) (m : MetricSpace β) :
    MetricSpace γ :=
  { PseudoMetricSpace.induced f m.toPseudoMetricSpace with
    eq_of_dist_eq_zero := fun h => hf (dist_eq_zero.1 h) }
#align metric_space.induced MetricSpace.induced

structure by a uniform embedding. This is a version of
`MetricSpace.induced` useful in case if the domain already has a `UniformSpace` structure. -/
@[reducible]
def UniformEmbedding.comapMetricSpace {α β} [UniformSpace α] [m : MetricSpace β] (f : α → β)
    (h : UniformEmbedding f) : MetricSpace α :=
  .replaceUniformity (.induced f h.inj m) h.comap_uniformity.symm
#align uniform_embedding.comap_metric_space UniformEmbedding.comapMetricSpace

structure by an embedding. This is a version of
`MetricSpace.induced` useful in case if the domain already has a `TopologicalSpace` structure. -/
@[reducible]
def Embedding.comapMetricSpace {α β} [TopologicalSpace α] [m : MetricSpace β] (f : α → β)
    (h : Embedding f) : MetricSpace α :=
  .replaceTopology (.induced f h.inj m) h.induced
#align embedding.comap_metric_space Embedding.comapMetricSpace