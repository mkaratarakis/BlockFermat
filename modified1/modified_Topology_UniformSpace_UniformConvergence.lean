def TendstoUniformlyOnFilter (F : ι → α → β) (f : α → β) (p : Filter ι) (p' : Filter α) :=
  ∀ u ∈ 𝓤 β, ∀ᶠ n : ι × α in p ×ˢ p', (f n.snd, F n.fst n.snd) ∈ u
#align tendsto_uniformly_on_filter TendstoUniformlyOnFilter

def TendstoUniformlyOn (F : ι → α → β) (f : α → β) (p : Filter ι) (s : Set α) :=
  ∀ u ∈ 𝓤 β, ∀ᶠ n in p, ∀ x : α, x ∈ s → (f x, F n x) ∈ u
#align tendsto_uniformly_on TendstoUniformlyOn

def TendstoUniformly (F : ι → α → β) (f : α → β) (p : Filter ι) :=
  ∀ u ∈ 𝓤 β, ∀ᶠ n in p, ∀ x : α, (f x, F n x) ∈ u
#align tendsto_uniformly TendstoUniformly

def UniformCauchySeqOnFilter (F : ι → α → β) (p : Filter ι) (p' : Filter α) : Prop :=
  ∀ u ∈ 𝓤 β, ∀ᶠ m : (ι × ι) × α in (p ×ˢ p) ×ˢ p', (F m.fst.fst m.snd, F m.fst.snd m.snd) ∈ u
#align uniform_cauchy_seq_on_filter UniformCauchySeqOnFilter

def UniformCauchySeqOn (F : ι → α → β) (p : Filter ι) (s : Set α) : Prop :=
  ∀ u ∈ 𝓤 β, ∀ᶠ m : ι × ι in p ×ˢ p, ∀ x : α, x ∈ s → (F m.fst x, F m.snd x) ∈ u
#align uniform_cauchy_seq_on UniformCauchySeqOn

def TendstoLocallyUniformlyOn (F : ι → α → β) (f : α → β) (p : Filter ι) (s : Set α) :=
  ∀ u ∈ 𝓤 β, ∀ x ∈ s, ∃ t ∈ 𝓝[s] x, ∀ᶠ n in p, ∀ y ∈ t, (f y, F n y) ∈ u
#align tendsto_locally_uniformly_on TendstoLocallyUniformlyOn

def TendstoLocallyUniformly (F : ι → α → β) (f : α → β) (p : Filter ι) :=
  ∀ u ∈ 𝓤 β, ∀ x : α, ∃ t ∈ 𝓝 x, ∀ᶠ n in p, ∀ y ∈ t, (f y, F n y) ∈ u
#align tendsto_locally_uniformly TendstoLocallyUniformly