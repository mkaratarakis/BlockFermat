def Filter.asBasis (f : Filter α) : FilterBasis α :=
  ⟨f.sets, ⟨univ, univ_mem⟩, fun {x y} hx hy => ⟨x ∩ y, inter_mem hx hy, subset_rfl⟩⟩
#align filter.as_basis Filter.asBasis

def filterBasis {p : ι → Prop} {s : ι → Set α} (h : IsBasis p s) : FilterBasis α where
  sets := { t | ∃ i, p i ∧ s i = t }
  nonempty :=
    let ⟨i, hi⟩ := h.nonempty
    ⟨s i, ⟨i, hi, rfl⟩⟩
  inter_sets := by
    rintro _ _ ⟨i, hi, rfl⟩ ⟨j, hj, rfl⟩
    rcases h.inter hi hj with ⟨k, hk, hk'⟩
    exact ⟨_, ⟨k, hk, rfl⟩, hk'⟩
#align filter.is_basis.filter_basis Filter.IsBasis.filterBasis

def filter (B : FilterBasis α) : Filter α where
  sets := { s | ∃ t ∈ B, t ⊆ s }
  univ_sets := B.nonempty.imp fun s s_in => ⟨s_in, s.subset_univ⟩
  sets_of_superset := fun ⟨s, s_in, h⟩ hxy => ⟨s, s_in, Set.Subset.trans h hxy⟩
  inter_sets := fun ⟨_s, s_in, hs⟩ ⟨_t, t_in, ht⟩ =>
    let ⟨u, u_in, u_sub⟩ := B.inter_sets s_in t_in
    ⟨u, u_in, u_sub.trans (inter_subset_inter hs ht)⟩
#align filter_basis.filter FilterBasis.filter

def filter (h : IsBasis p s) : Filter α :=
  h.filterBasis.filter
#align filter.is_basis.filter Filter.IsBasis.filter

def FilterBasis.ofSets (s : Set (Set α)) : FilterBasis α where
  sets := sInter '' { t | Set.Finite t ∧ t ⊆ s }
  nonempty := ⟨univ, ∅, ⟨⟨finite_empty, empty_subset s⟩, sInter_empty⟩⟩
  inter_sets := by
    rintro _ _ ⟨a, ⟨fina, suba⟩, rfl⟩ ⟨b, ⟨finb, subb⟩, rfl⟩
    exact ⟨⋂₀ (a ∪ b), mem_image_of_mem _ ⟨fina.union finb, union_subset suba subb⟩,
        (sInter_union _ _).subset⟩
#align filter.filter_basis.of_sets Filter.FilterBasis.ofSets

def HasBasis.index (h : l.HasBasis p s) (t : Set α) (ht : t ∈ l) : { i : ι // p i } :=
  ⟨(h.mem_iff.1 ht).choose, (h.mem_iff.1 ht).choose_spec.1⟩
#align filter.has_basis.index Filter.HasBasis.index

structure FilterBasis (α : Type*) where
  /-- Sets of a filter basis. -/
  sets : Set (Set α)
  /-- The set of filter basis sets is nonempty. -/
  nonempty : sets.Nonempty
  /-- The set of filter basis sets is directed downwards. -/
  inter_sets {x y} : x ∈ sets → y ∈ sets → ∃ z ∈ sets, z ⊆ x ∩ y
#align filter_basis FilterBasis

structure Filter.IsBasis (p : ι → Prop) (s : ι → Set α) : Prop where
  /-- There exists at least one `i` that satisfies `p`. -/
  nonempty : ∃ i, p i
  /-- `s` is directed downwards on `i` such that `p i`. -/
  inter : ∀ {i j}, p i → p j → ∃ k, p k ∧ s k ⊆ s i ∩ s j
#align filter.is_basis Filter.IsBasis

structure HasBasis (l : Filter α) (p : ι → Prop) (s : ι → Set α) : Prop where
  /-- A set `t` belongs to a filter `l` iff it includes an element of the basis. -/
  mem_iff' : ∀ t : Set α, t ∈ l ↔ ∃ i, p i ∧ s i ⊆ t
#align filter.has_basis Filter.HasBasis

structure IsAntitoneBasis extends IsBasis (fun _ => True) s'' : Prop where
  /-- The sequence of sets is antitone. -/
  protected antitone : Antitone s''
#align filter.is_antitone_basis Filter.IsAntitoneBasis

structure HasAntitoneBasis (l : Filter α) (s : ι'' → Set α)
    extends HasBasis l (fun _ => True) s : Prop where
  /-- The sequence of sets is antitone. -/
  protected antitone : Antitone s
#align filter.has_antitone_basis Filter.HasAntitoneBasis

structure IsCountableBasis (p : ι → Prop) (s : ι → Set α) extends IsBasis p s : Prop where
  /-- The set of `i` that satisfy the predicate `p` is countable. -/
  countable : (setOf p).Countable
#align filter.is_countable_basis Filter.IsCountableBasis

structure HasCountableBasis (l : Filter α) (p : ι → Prop) (s : ι → Set α)
    extends HasBasis l p s : Prop where
  /-- The set of `i` that satisfy the predicate `p` is countable. -/
  countable : (setOf p).Countable
#align filter.has_countable_basis Filter.HasCountableBasis

structure CountableFilterBasis (α : Type*) extends FilterBasis α where
  /-- The set of sets of the filter basis is countable. -/
  countable : sets.Countable
#align filter.countable_filter_basis Filter.CountableFilterBasis