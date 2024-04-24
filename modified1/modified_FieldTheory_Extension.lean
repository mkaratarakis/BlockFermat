structure Lifts where
  /-- The domain of a lift. -/
  carrier : IntermediateField F E
  /-- The lifted RingHom, expressed as an AlgHom. -/
  emb : carrier →ₐ[F] K
#align intermediate_field.lifts IntermediateField.Lifts