def CofiniteTopology (X : Type*) := X

#align cofinite_topology CofiniteTopology

def of : X ≃ CofiniteTopology X :=
  Equiv.refl X
#align cofinite_topology.of CofiniteTopology.of

structure on topologies. Their universal properties
(for example, a map `X → Y × Z` is continuous if and only if both projections
`X → Y`, `X → Z` are) follow easily using order-theoretic descriptions of
continuity. With more work we can also extract descriptions of the open sets,
neighborhood filters and so on.

## Tags