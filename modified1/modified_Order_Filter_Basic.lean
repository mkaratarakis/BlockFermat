def copy (f : Filter α) (S : Set (Set α)) (hmem : ∀ s, s ∈ S ↔ s ∈ f) : Filter α where
  sets := S
  univ_sets := (hmem _).2 univ_mem
  sets_of_superset h hsub := (hmem _).2 <| mem_of_superset ((hmem _).1 h) hsub
  inter_sets h₁ h₂ := (hmem _).2 <| inter_mem ((hmem _).1 h₁) ((hmem _).1 h₂)

lemma copy_eq {S} (hmem : ∀ s, s ∈ S ↔ s ∈ f) : f.copy S hmem = f := Filter.ext hmem

@[simp] lemma mem_copy {S hmem} : s ∈ f.copy S hmem ↔ s ∈ S := Iff.rfl

@[simp]
theorem biInter_mem {β : Type v} {s : β → Set α} {is : Set β} (hf : is.Finite) :
    (⋂ i ∈ is, s i) ∈ f ↔ ∀ i ∈ is, s i ∈ f :=
  Finite.induction_on hf (by simp) fun _ _ hs => by simp [hs]
#align filter.bInter_mem Filter.biInter_mem

def principal (s : Set α) : Filter α where
  sets := { t | s ⊆ t }
  univ_sets := subset_univ s
  sets_of_superset hx := Subset.trans hx
  inter_sets := subset_inter
#align filter.principal Filter.principal

def join (f : Filter (Filter α)) : Filter α where
  sets := { s | { t : Filter α | s ∈ t } ∈ f }
  univ_sets := by simp only [mem_setOf_eq, univ_sets, ← Filter.mem_sets, setOf_true]
  sets_of_superset hx xy := mem_of_superset hx fun f h => mem_of_superset h xy
  inter_sets hx hy := mem_of_superset (inter_mem hx hy) fun f ⟨h₁, h₂⟩ => inter_mem h₁ h₂
#align filter.join Filter.join

def : f ≤ g ↔ ∀ x ∈ g, x ∈ f :=
  Iff.rfl
#align filter.le_def Filter.le_def

def generate (g : Set (Set α)) : Filter α where
  sets := {s | GenerateSets g s}
  univ_sets := GenerateSets.univ
  sets_of_superset := GenerateSets.superset
  inter_sets := GenerateSets.inter
#align filter.generate Filter.generate

def mkOfClosure (s : Set (Set α)) (hs : (generate s).sets = s) : Filter α where
  sets := s
  univ_sets := hs ▸ univ_mem
  sets_of_superset := hs ▸ mem_of_superset
  inter_sets := hs ▸ inter_mem
#align filter.mk_of_closure Filter.mkOfClosure

def giGenerate (α : Type*) :
    @GaloisInsertion (Set (Set α)) (Filter α)ᵒᵈ _ _ Filter.generate Filter.sets where
  gc _ _ := le_generate_iff
  le_l_u _ _ h := GenerateSets.basic h
  choice s hs := Filter.mkOfClosure s (le_antisymm hs <| le_generate_iff.1 <| le_rfl)
  choice_eq _ _ := mkOfClosure_sets
#align filter.gi_generate Filter.giGenerate

def Eventually (p : α → Prop) (f : Filter α) : Prop :=
  { x | p x } ∈ f
#align filter.eventually Filter.Eventually

def Frequently (p : α → Prop) (f : Filter α) : Prop :=
  ¬∀ᶠ x in f, ¬p x
#align filter.frequently Filter.Frequently

def EventuallyEq (l : Filter α) (f g : α → β) : Prop :=
  ∀ᶠ x in l, f x = g x
#align filter.eventually_eq Filter.EventuallyEq

def EventuallyLE (l : Filter α) (f g : α → β) : Prop :=
  ∀ᶠ x in l, f x ≤ g x
#align filter.eventually_le Filter.EventuallyLE

def map (m : α → β) (f : Filter α) : Filter β where
  sets := preimage m ⁻¹' f.sets
  univ_sets := univ_mem
  sets_of_superset hs st := mem_of_superset hs <| preimage_mono st
  inter_sets hs ht := inter_mem hs ht
#align filter.map Filter.map

def comap (m : α → β) (f : Filter β) : Filter α
    where
  sets := { s | ∃ t ∈ f, m ⁻¹' t ⊆ s }
  univ_sets := ⟨univ, univ_mem, by simp only [subset_univ, preimage_univ]⟩
  sets_of_superset := fun ⟨a', ha', ma'a⟩ ab => ⟨a', ha', ma'a.trans ab⟩
  inter_sets := fun ⟨a', ha₁, ha₂⟩ ⟨b', hb₁, hb₂⟩ =>
    ⟨a' ∩ b', inter_mem ha₁ hb₁, inter_subset_inter ha₂ hb₂⟩
#align filter.comap Filter.comap

def kernMap (m : α → β) (f : Filter α) : Filter β where
  sets := (kernImage m) '' f.sets
  univ_sets := ⟨univ, f.univ_sets, by simp [kernImage_eq_compl]⟩
  sets_of_superset := by
    rintro _ t ⟨s, hs, rfl⟩ hst
    refine ⟨s ∪ m ⁻¹' t, mem_of_superset hs (subset_union_left s _), ?_⟩
    rw [kernImage_union_preimage, union_eq_right.mpr hst]
  inter_sets := by
    rintro _ _ ⟨s₁, h₁, rfl⟩ ⟨s₂, h₂, rfl⟩
    exact ⟨s₁ ∩ s₂, f.inter_sets h₁ h₂, Set.preimage_kernImage.u_inf⟩

variable {m : α → β} {f : Filter α}

theorem mem_kernMap {s : Set β} : s ∈ kernMap m f ↔ ∃ t ∈ f, kernImage m t = s :=
  Iff.rfl

theorem mem_kernMap_iff_compl {s : Set β} : s ∈ kernMap m f ↔ ∃ t, tᶜ ∈ f ∧ m '' t = sᶜ := by
  rw [mem_kernMap, compl_surjective.exists]
  refine exists_congr (fun x ↦ and_congr_right fun _ ↦ ?_)
  rw [kernImage_compl, compl_eq_comm, eq_comm]

theorem compl_mem_kernMap {s : Set β} : sᶜ ∈ kernMap m f ↔ ∃ t, tᶜ ∈ f ∧ m '' t = s := by
  simp_rw [mem_kernMap_iff_compl, compl_compl]

end KernMap

/-- The monadic bind operation on filter is defined the usual way in terms of `map` and `join`.

Unfortunately, this `bind` does not result in the expected applicative. See `Filter.seq` for the
applicative instance. -/
def bind (f : Filter α) (m : α → Filter β) : Filter β :=
  join (map m f)
#align filter.bind Filter.bind

def seq (f : Filter (α → β)) (g : Filter α) : Filter β where
  sets := { s | ∃ u ∈ f, ∃ t ∈ g, ∀ m ∈ u, ∀ x ∈ t, (m : α → β) x ∈ s }
  univ_sets := ⟨univ, univ_mem, univ, univ_mem, fun _ _ _ _ => trivial⟩
  sets_of_superset := fun ⟨t₀, t₁, h₀, h₁, h⟩ hst =>
    ⟨t₀, t₁, h₀, h₁, fun _ hx _ hy => hst <| h _ hx _ hy⟩
  inter_sets := fun ⟨t₀, ht₀, t₁, ht₁, ht⟩ ⟨u₀, hu₀, u₁, hu₁, hu⟩ =>
    ⟨t₀ ∩ u₀, inter_mem ht₀ hu₀, t₁ ∩ u₁, inter_mem ht₁ hu₁, fun _ ⟨hx₀, hx₁⟩ _ ⟨hy₀, hy₁⟩ =>
      ⟨ht _ hx₀ _ hy₀, hu _ hx₁ _ hy₁⟩⟩
#align filter.seq Filter.seq

def monad : Monad Filter where map := @Filter.map
#align filter.monad Filter.monad

def {α β} (m : α → β) (f : Filter α) : m <$> f = map m f :=
  rfl
#align filter.map_def Filter.map_def

def {α β} (f : Filter α) (m : α → Filter β) : f >>= m = bind f m :=
  rfl
#align filter.bind_def Filter.bind_def

def {f : Filter (α → β)} {g : Filter α} {s : Set β} :
    s ∈ f.seq g ↔ ∃ u ∈ f, ∃ t ∈ g, ∀ x ∈ u, ∀ y ∈ t, (x : α → β) y ∈ s :=
  Iff.rfl
#align filter.mem_seq_def Filter.mem_seq_def

def Tendsto (f : α → β) (l₁ : Filter α) (l₂ : Filter β) :=
  l₁.map f ≤ l₂
#align filter.tendsto Filter.Tendsto

def {f : α → β} {l₁ : Filter α} {l₂ : Filter β} :
    Tendsto f l₁ l₂ ↔ ∀ s ∈ l₂, f ⁻¹' s ∈ l₁ :=
  Iff.rfl
#align filter.tendsto_def Filter.tendsto_def

structure is lifted from the lattice structure on `Set (Set X)` using the Galois
insertion which maps a filter to its elements in one direction, and an arbitrary set of sets to
the smallest filter containing it in the other direction.
We also prove `Filter` is a monadic functor, with a push-forward operation
`Filter.map` and a pull-back operation `Filter.comap` that form a Galois connections for the
order on filters.

The examples of filters appearing in the description of the two motivating ideas are:
* `(Filter.atTop : Filter ℕ)` : made of sets of `ℕ` containing `{n | n ≥ N}` for some `N`
* `𝓝 x` : made of neighborhoods of `x` in a topological space (defined in topology.basic)
* `𝓤 X` : made of entourages of a uniform space (those space are generalizations of metric spaces
  defined in `Mathlib/Topology/UniformSpace/Basic.lean`)
* `μ.ae` : made of sets whose complement has zero measure with respect to `μ` (defined in
  `MeasureTheory.MeasureSpace`)

The general notion of limit of a map with respect to filters on the source and target types
is `Filter.Tendsto`. It is defined in terms of the order and the push-forward operation.
The predicate "happening eventually" is `Filter.Eventually`, and "happening often" is
`Filter.Frequently`, whose definitions are immediate after `Filter` is defined (but they come
rather late in this file in order to immediately relate them to the lattice structure).

For instance, anticipating on Topology.Basic, the statement: "if a sequence `u` converges to
some `x` and `u n` belongs to a set `M` for `n` large enough then `x` is in the closure of
`M`" is formalized as: `Tendsto u atTop (𝓝 x) → (∀ᶠ n in atTop, u n ∈ M) → x ∈ closure M`,
which is a special case of `mem_closure_of_tendsto` from Topology.Basic.

## Notations

structure Filter (α : Type*) where
  /-- The set of sets that belong to the filter. -/
  sets : Set (Set α)
  /-- The set `Set.univ` belongs to any filter. -/
  univ_sets : Set.univ ∈ sets
  /-- If a set belongs to a filter, then its superset belongs to the filter as well. -/
  sets_of_superset {x y} : x ∈ sets → x ⊆ y → y ∈ sets
  /-- If two sets belong to a filter, then their intersection belongs to the filter as well. -/
  inter_sets {x y} : x ∈ sets → y ∈ sets → x ∩ y ∈ sets
#align filter Filter

structure on `Filter _`, so we use a typeclass argument in lemmas instead. -/
class NeBot (f : Filter α) : Prop where
  /-- The filter is nontrivial: `f ≠ ⊥` or equivalently, `∅ ∉ f`. -/
  ne' : f ≠ ⊥
#align filter.ne_bot Filter.NeBot

structure -/

section Map

/-- The forward map of a filter -/
def map (m : α → β) (f : Filter α) : Filter β where
  sets := preimage m ⁻¹' f.sets
  univ_sets := univ_mem
  sets_of_superset hs st := mem_of_superset hs <| preimage_mono st
  inter_sets hs ht := inter_mem hs ht
#align filter.map Filter.map

structure on `Filter`s. This definition is not
an instance because its `Seq` projection is not equal to the `Filter.seq` function we use in the
`Applicative` instance on `Filter`.
-/

section

/-- The monad structure on filters. -/
protected def monad : Monad Filter where map := @Filter.map
#align filter.monad Filter.monad