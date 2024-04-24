def Embedding.comapUniformSpace {α β} [TopologicalSpace α] [u : UniformSpace β] (f : α → β)
    (h : Embedding f) : UniformSpace α :=
  (u.comap f).replaceTopology h.induced
#align embedding.comap_uniform_space Embedding.comapUniformSpace

structure UniformInducing (f : α → β) : Prop where
  /-- The uniformity filter on the domain is the pullback of the uniformity filter on the codomain
  under `Prod.map f f`. -/
  comap_uniformity : comap (fun x : α × α => (f x.1, f x.2)) (𝓤 β) = 𝓤 α
#align uniform_inducing UniformInducing

structure UniformEmbedding (f : α → β) extends UniformInducing f : Prop where
  /-- A uniform embedding is injective. -/
  inj : Function.Injective f
#align uniform_embedding UniformEmbedding

structure by an embedding, adjusting the new uniform structure to
make sure that its topology is defeq to the original one. -/
def Embedding.comapUniformSpace {α β} [TopologicalSpace α] [u : UniformSpace β] (f : α → β)
    (h : Embedding f) : UniformSpace α :=
  (u.comap f).replaceTopology h.induced
#align embedding.comap_uniform_space Embedding.comapUniformSpace