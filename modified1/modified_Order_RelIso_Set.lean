def Subrel (r : α → α → Prop) (p : Set α) : p → p → Prop :=
  (Subtype.val : p → α) ⁻¹'o r
#align subrel Subrel

def relEmbedding (r : α → α → Prop) (p : Set α) : Subrel r p ↪r r :=
  ⟨Embedding.subtype _, Iff.rfl⟩
#align subrel.rel_embedding Subrel.relEmbedding

def RelEmbedding.codRestrict (p : Set β) (f : r ↪r s) (H : ∀ a, f a ∈ p) : r ↪r Subrel s p :=
  ⟨f.toEmbedding.codRestrict p H, f.map_rel_iff'⟩
#align rel_embedding.cod_restrict RelEmbedding.codRestrict