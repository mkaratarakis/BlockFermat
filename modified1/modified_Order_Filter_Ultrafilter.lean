def ofComplNotMemIff (f : Filter α) (h : ∀ s, sᶜ ∉ f ↔ s ∈ f) : Ultrafilter α where
  toFilter := f
  neBot' := ⟨fun hf => by simp [hf] at h⟩
  le_of_le g hg hgf s hs := (h s).1 fun hsc => compl_not_mem hs (hgf hsc)
#align ultrafilter.of_compl_not_mem_iff Ultrafilter.ofComplNotMemIff

def ofAtom (f : Filter α) (hf : IsAtom f) : Ultrafilter α where
  toFilter := f
  neBot' := ⟨hf.1⟩
  le_of_le g hg := (isAtom_iff_le_of_ge.1 hf).2 g hg.ne
#align ultrafilter.of_atom Ultrafilter.ofAtom

def map (m : α → β) (f : Ultrafilter α) : Ultrafilter β :=
  ofComplNotMemIff (map m f) fun s => @compl_not_mem_iff _ f (m ⁻¹' s)
#align ultrafilter.map Ultrafilter.map

def comap {m : α → β} (u : Ultrafilter β) (inj : Injective m) (large : Set.range m ∈ u) :
    Ultrafilter α where
  toFilter := comap m u
  neBot' := u.neBot'.comap_of_range_mem large
  le_of_le g hg hgu := by
    simp only [← u.unique (map_le_iff_le_comap.2 hgu), comap_map inj, le_rfl]
#align ultrafilter.comap Ultrafilter.comap

def bind (f : Ultrafilter α) (m : α → Ultrafilter β) : Ultrafilter β :=
  ofComplNotMemIff (Filter.bind ↑f fun x => ↑(m x)) fun s => by
    simp only [mem_bind', mem_coe, ← compl_mem_iff_not_mem, compl_setOf, compl_compl]
#align ultrafilter.bind Ultrafilter.bind

def of (f : Filter α) [NeBot f] : Ultrafilter α :=
  Classical.choose (exists_le f)
#align ultrafilter.of Ultrafilter.of

def hyperfilter : Ultrafilter α :=
  Ultrafilter.of cofinite
#align filter.hyperfilter Filter.hyperfilter

def ofComapInfPrincipal (h : m '' s ∈ g) : Ultrafilter α :=
  @of _ (Filter.comap m g ⊓ 𝓟 s) (comap_inf_principal_neBot_of_image_mem h)
#align ultrafilter.of_comap_inf_principal Ultrafilter.ofComapInfPrincipal

structure Ultrafilter (α : Type*) extends Filter α where
  /-- An ultrafilter is nontrivial. -/
  protected neBot' : NeBot toFilter
  /-- If `g` is a nontrivial filter that is less than or equal to an ultrafilter, then it is greater
  than or equal to the ultrafilter. -/
  protected le_of_le : ∀ g, Filter.NeBot g → g ≤ toFilter → toFilter ≤ g
#align ultrafilter Ultrafilter