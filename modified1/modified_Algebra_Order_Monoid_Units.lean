def orderEmbeddingVal [Monoid α] [LinearOrder α] : αˣ ↪o α :=
  ⟨⟨val, ext⟩, Iff.rfl⟩
#align units.order_embedding_coe Units.orderEmbeddingVal