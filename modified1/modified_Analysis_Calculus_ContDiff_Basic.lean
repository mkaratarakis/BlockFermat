def restrContDiff (f : PartialHomeomorph E F) (n : ℕ) : PartialHomeomorph E F :=
  haveI H : f.IsImage {x | ContDiffAt 𝕜 n f x ∧ ContDiffAt 𝕜 n f.symm (f x)}
      {y | ContDiffAt 𝕜 n f.symm y ∧ ContDiffAt 𝕜 n f (f.symm y)} := fun x hx ↦ by
    simp [hx, and_comm]
  H.restr <| isOpen_iff_mem_nhds.2 fun x ⟨hxs, hxf, hxf'⟩ ↦
    inter_mem (f.open_source.mem_nhds hxs) <| hxf.eventually.and <|
    f.continuousAt hxs hxf'.eventually

lemma contDiffOn_restrContDiff_source (f : PartialHomeomorph E F) (n : ℕ) :
    ContDiffOn 𝕜 n f (f.restrContDiff 𝕜 n).source := fun _x hx ↦ hx.2.1.contDiffWithinAt

lemma contDiffOn_restrContDiff_target (f : PartialHomeomorph E F) (n : ℕ) :
    ContDiffOn 𝕜 n f.symm (f.restrContDiff 𝕜 n).target := fun _x hx ↦ hx.2.1.contDiffWithinAt

end PartialHomeomorph

end FunctionInverse

section deriv

/-!
### One dimension