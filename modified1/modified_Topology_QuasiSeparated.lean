def IsQuasiSeparated (s : Set α) : Prop :=
  ∀ U V : Set α, U ⊆ s → IsOpen U → IsCompact U → V ⊆ s → IsOpen V → IsCompact V → IsCompact (U ∩ V)
#align is_quasi_separated IsQuasiSeparated