def toLocallyBoundedMap (f : α → β) (hf : LipschitzWith K f) : LocallyBoundedMap α β :=
  LocallyBoundedMap.ofMapBounded f fun _s hs =>
    let ⟨C, hC⟩ := Metric.isBounded_iff.1 hs
    Metric.isBounded_iff.2 ⟨K * C, forall_mem_image.2 fun _x hx => forall_mem_image.2 fun _y hy =>
      hf.dist_le_mul_of_le (hC hx hy)⟩
#align lipschitz_with.to_locally_bounded_map LipschitzWith.toLocallyBoundedMap