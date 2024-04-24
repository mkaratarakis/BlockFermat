def generateFrom (g : Set (Set α)) : TopologicalSpace α where
  IsOpen := GenerateOpen g
  isOpen_univ := GenerateOpen.univ
  isOpen_inter := GenerateOpen.inter
  isOpen_sUnion := GenerateOpen.sUnion
#align topological_space.generate_from TopologicalSpace.generateFrom

def mkOfNhds (n : α → Filter α) : TopologicalSpace α where
  IsOpen s := ∀ a ∈ s, s ∈ n a
  isOpen_univ _ _ := univ_mem
  isOpen_inter := fun _s _t hs ht x ⟨hxs, hxt⟩ => inter_mem (hs x hxs) (ht x hxt)
  isOpen_sUnion := fun _s hs _a ⟨x, hx, hxa⟩ =>
    mem_of_superset (hs x hx _ hxa) (subset_sUnion_of_mem hx)
#align topological_space.mk_of_nhds TopologicalSpace.mkOfNhds

def {α} {t s : TopologicalSpace α} : t ≤ s ↔ IsOpen[s] ≤ IsOpen[t] :=
  Iff.rfl
#align topological_space.le_def TopologicalSpace.le_def

def mkOfClosure (s : Set (Set α)) (hs : { u | GenerateOpen s u } = s) :
    TopologicalSpace α where
  IsOpen u := u ∈ s
  isOpen_univ := hs ▸ TopologicalSpace.GenerateOpen.univ
  isOpen_inter := hs ▸ TopologicalSpace.GenerateOpen.inter
  isOpen_sUnion := hs ▸ TopologicalSpace.GenerateOpen.sUnion
#align topological_space.mk_of_closure TopologicalSpace.mkOfClosure

def gciGenerateFrom (α : Type*) :
    GaloisCoinsertion (fun t : TopologicalSpace α => OrderDual.toDual { s | IsOpen[t] s })
      (generateFrom ∘ OrderDual.ofDual) where
  gc := gc_generateFrom α
  u_l_le _ s hs := TopologicalSpace.GenerateOpen.basic s hs
  choice g hg := TopologicalSpace.mkOfClosure g
    (Subset.antisymm hg <| le_generateFrom_iff_subset_isOpen.1 <| le_rfl)
  choice_eq _ _ := mkOfClosure_sets
#align gi_generate_from TopologicalSpace.gciGenerateFrom

def α β t t').1 h
#align continuous.coinduced_le Continuous.coinduced_le

def nhdsAdjoint (a : α) (f : Filter α) : TopologicalSpace α where
  IsOpen s := a ∈ s → s ∈ f
  isOpen_univ _ := univ_mem
  isOpen_inter := fun _s _t hs ht ⟨has, hat⟩ => inter_mem (hs has) (ht hat)
  isOpen_sUnion := fun _k hk ⟨u, hu, hau⟩ => mem_of_superset (hk u hu hau) (subset_sUnion_of_mem hu)
#align nhds_adjoint nhdsAdjoint

def
#align continuous_iff_coinduced_le continuous_iff_coinduced_le

def _ _ t t' id
#align continuous_id_iff_le continuous_id_iff_le

structure on topologies on `α` is defined as the
reverse of the one obtained via this Galois insertion. More precisely, we use the corresponding
Galois coinsertion between topologies on `α` (with the reversed inclusion ordering) and collections
of sets in `α` (with the reversed inclusion ordering).

## Tags

structure on a type with discrete topology is equal to `⊥`. -/
  eq_bot : t = ⊥
#align discrete_topology DiscreteTopology

structure
section Constructions

open TopologicalSpace

variable {α : Type u} {β : Type v}

instance inhabitedTopologicalSpace {α : Type u} : Inhabited (TopologicalSpace α) :=
  ⟨⊥⟩
#align inhabited_topological_space inhabitedTopologicalSpace