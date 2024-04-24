def TopologicalSpace.ofClosed {X : Type u} (T : Set (Set X)) (empty_mem : ∅ ∈ T)
    (sInter_mem : ∀ A, A ⊆ T → ⋂₀ A ∈ T)
    (union_mem : ∀ A, A ∈ T → ∀ B, B ∈ T → A ∪ B ∈ T) : TopologicalSpace X where
  IsOpen X := Xᶜ ∈ T
  isOpen_univ := by simp [empty_mem]
  isOpen_inter s t hs ht := by simpa only [compl_inter] using union_mem sᶜ hs tᶜ ht
  isOpen_sUnion s hs := by
    simp only [Set.compl_sUnion]
    exact sInter_mem (compl '' s) fun z ⟨y, hy, hz⟩ => hz ▸ hs y hy
#align topological_space.of_closed TopologicalSpace.ofClosed

def {ι : Type*} (x : X) (F : Filter ι) (u : ι → X) :
    MapClusterPt x F u ↔ ClusterPt x (map u F) := Iff.rfl

theorem mapClusterPt_iff {ι : Type*} (x : X) (F : Filter ι) (u : ι → X) :
    MapClusterPt x F u ↔ ∀ s ∈ 𝓝 x, ∃ᶠ a in F, u a ∈ s := by
  simp_rw [MapClusterPt, ClusterPt, inf_neBot_iff_frequently_left, frequently_map]
  rfl
#align map_cluster_pt_iff mapClusterPt_iff

def {_ : TopologicalSpace X} {_ : TopologicalSpace Y} {f : X → Y} :
    Continuous f ↔ ∀ s, IsOpen s → IsOpen (f ⁻¹' s) :=
  ⟨fun hf => hf.1, fun h => ⟨h⟩⟩
#align continuous_def continuous_def

def : ContinuousAt f x ↔ ∀ A ∈ 𝓝 (f x), f ⁻¹' A ∈ 𝓝 x :=
  Iff.rfl
#align continuous_at_def continuousAt_def

def DenseRange.some (hf : DenseRange f) (x : X) : α :=
  Classical.choice <| hf.nonempty_iff.mpr ⟨x⟩
#align dense_range.some DenseRange.some

def strans {x : F} (γ γ' : Path x x) (t₀ : I) : Path x x
```
The precise definition is not important, only its type.
The correct continuity principle for this operation is something like this:
```
{f : X → F} {γ γ' : ∀ x, Path (f x) (f x)} {t₀ s : X → I}
  (hγ : Continuous ↿γ) (hγ' : Continuous ↿γ')
  (ht : Continuous t₀) (hs : Continuous s) :
  Continuous (fun x ↦ strans (γ x) (γ' x) (t x) (s x))
```
Note that *all* arguments of `strans` are indexed over `X`, even the basepoint `x`, and the last
argument `s` that arises since `Path x x` has a coercion to `I → F`. The paths `γ` and `γ'` (which
are unary functions from `I`) become binary functions in the continuity lemma.

### Summary