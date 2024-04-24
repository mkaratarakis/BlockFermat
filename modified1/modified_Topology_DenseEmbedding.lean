def extend (di : DenseInducing i) (f : α → γ) (b : β) : γ :=
  @limUnder _ _ _ ⟨f (di.dense.some b)⟩ (comap i (𝓝 b)) f
#align dense_inducing.extend DenseInducing.extend

def subtypeEmb {α : Type*} (p : α → Prop) (e : α → β) (x : { x // p x }) :
    { x // x ∈ closure (e '' { x | p x }) } :=
  ⟨e x, subset_closure <| mem_image_of_mem e x.prop⟩
#align dense_embedding.subtype_emb DenseEmbedding.subtypeEmb

structure DenseInducing [TopologicalSpace α] [TopologicalSpace β] (i : α → β)
    extends Inducing i : Prop where
  /-- The range of a dense inducing map is a dense set. -/
  protected dense : DenseRange i
#align dense_inducing DenseInducing

structure DenseEmbedding [TopologicalSpace α] [TopologicalSpace β] (e : α → β) extends
  DenseInducing e : Prop where
  /-- A dense embedding is injective. -/
  inj : Function.Injective e
#align dense_embedding DenseEmbedding