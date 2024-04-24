def ZeroAtFilter [Zero β] [TopologicalSpace β] (l : Filter α) (f : α → β) : Prop :=
  Filter.Tendsto f l (𝓝 0)
#align filter.zero_at_filter Filter.ZeroAtFilter

def zeroAtFilterSubmodule
    [TopologicalSpace β] [Semiring 𝕜] [AddCommMonoid β] [Module 𝕜 β]
    [ContinuousAdd β] [ContinuousConstSMul 𝕜 β]
    (l : Filter α) : Submodule 𝕜 (α → β) where
  carrier := ZeroAtFilter l
  zero_mem' := zero_zeroAtFilter l
  add_mem' ha hb := ha.add hb
  smul_mem' c _ hf := hf.smul c
#align filter.zero_at_filter_submodule Filter.zeroAtFilterSubmodule

def zeroAtFilterAddSubmonoid [TopologicalSpace β] [AddZeroClass β] [ContinuousAdd β]
    (l : Filter α) : AddSubmonoid (α → β) where
  carrier := ZeroAtFilter l
  add_mem' ha hb := ha.add hb
  zero_mem' := zero_zeroAtFilter l
#align filter.zero_at_filter_add_submonoid Filter.zeroAtFilterAddSubmonoid

def BoundedAtFilter [Norm β] (l : Filter α) (f : α → β) : Prop :=
  Asymptotics.IsBigO l f (1 : α → ℝ)
#align filter.bounded_at_filter Filter.BoundedAtFilter

def boundedFilterSubmodule
    [SeminormedRing 𝕜] [SeminormedAddCommGroup β] [Module 𝕜 β] [BoundedSMul 𝕜 β] (l : Filter α) :
    Submodule 𝕜 (α → β) where
  carrier := BoundedAtFilter l
  zero_mem' := const_boundedAtFilter l 0
  add_mem' hf hg := hf.add hg
  smul_mem' c _ hf := hf.smul c
#align filter.bounded_filter_submodule Filter.boundedFilterSubmodule

def boundedFilterSubalgebra
    [SeminormedCommRing 𝕜] [SeminormedRing β] [Algebra 𝕜 β] [BoundedSMul 𝕜 β] (l : Filter α) :
    Subalgebra 𝕜 (α → β) :=
  Submodule.toSubalgebra
    (boundedFilterSubmodule 𝕜 l)
    (const_boundedAtFilter l (1 : β))
    (fun f g hf hg ↦ by simpa only [Pi.one_apply, mul_one, norm_mul] using hf.mul hg)
#align filter.bounded_filter_subalgebra Filter.boundedFilterSubalgebra