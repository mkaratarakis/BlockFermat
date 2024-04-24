def length : ℕ :=
  c.blocks.length
#align composition.length Composition.length

def blocksFun : Fin c.length → ℕ := c.blocks.get
#align composition.blocks_fun Composition.blocksFun

def sizeUpTo (i : ℕ) : ℕ :=
  (c.blocks.take i).sum
#align composition.size_up_to Composition.sizeUpTo

def boundary : Fin (c.length + 1) ↪o Fin (n + 1) :=
  (OrderEmbedding.ofStrictMono fun i => ⟨c.sizeUpTo i, Nat.lt_succ_of_le (c.sizeUpTo_le i)⟩) <|
    Fin.strictMono_iff_lt_succ.2 fun ⟨_, hi⟩ => c.sizeUpTo_strict_mono hi
#align composition.boundary Composition.boundary

def boundaries : Finset (Fin (n + 1)) :=
  Finset.univ.map c.boundary.toEmbedding
#align composition.boundaries Composition.boundaries

def toCompositionAsSet : CompositionAsSet n
    where
  boundaries := c.boundaries
  zero_mem := by
    simp only [boundaries, Finset.mem_univ, exists_prop_of_true, Finset.mem_map]
    exact ⟨0, And.intro True.intro rfl⟩
  getLast_mem := by
    simp only [boundaries, Finset.mem_univ, exists_prop_of_true, Finset.mem_map]
    exact ⟨Fin.last c.length, And.intro True.intro c.boundary_last⟩
#align composition.to_composition_as_set Composition.toCompositionAsSet

def embedding (i : Fin c.length) : Fin (c.blocksFun i) ↪o Fin n :=
  (Fin.natAddEmb <| c.sizeUpTo i).trans <|
    Fin.castLEEmb <|
      calc
        c.sizeUpTo i + c.blocksFun i = c.sizeUpTo (i + 1) := (c.sizeUpTo_succ _).symm
        _ ≤ c.sizeUpTo c.length := monotone_sum_take _ i.2
        _ = n := c.sizeUpTo_length
#align composition.embedding Composition.embedding

def index (j : Fin n) : Fin c.length :=
  ⟨Nat.find (c.index_exists j.2), (Nat.find_spec (c.index_exists j.2)).2⟩
#align composition.index Composition.index

def invEmbedding (j : Fin n) : Fin (c.blocksFun (c.index j)) :=
  ⟨j - c.sizeUpTo (c.index j), by
    rw [tsub_lt_iff_right, add_comm, ← sizeUpTo_succ']
    · exact lt_sizeUpTo_index_succ _ _
    · exact sizeUpTo_index_le _ _⟩
#align composition.inv_embedding Composition.invEmbedding

def blocksFinEquiv : (Σi : Fin c.length, Fin (c.blocksFun i)) ≃ Fin n
    where
  toFun x := c.embedding x.1 x.2
  invFun j := ⟨c.index j, c.invEmbedding j⟩
  left_inv x := by
    rcases x with ⟨i, y⟩
    dsimp
    congr; · exact c.index_embedding _ _
    rw [Fin.heq_ext_iff]
    · exact c.invEmbedding_comp _ _
    · rw [c.index_embedding]
  right_inv j := c.embedding_comp_inv j
#align composition.blocks_fin_equiv Composition.blocksFinEquiv

def ones (n : ℕ) : Composition n :=
  ⟨replicate n (1 : ℕ), fun {i} hi => by simp [List.eq_of_mem_replicate hi], by simp⟩
#align composition.ones Composition.ones

def single (n : ℕ) (h : 0 < n) : Composition n :=
  ⟨[n], by simp [h], by simp⟩
#align composition.single Composition.single

def splitWrtCompositionAux : List α → List ℕ → List (List α)
  | _, [] => []
  | l, n::ns =>
    let (l₁, l₂) := l.splitAt n
    l₁::splitWrtCompositionAux l₂ ns
#align list.split_wrt_composition_aux List.splitWrtCompositionAux

def splitWrtComposition (l : List α) (c : Composition n) : List (List α) :=
  splitWrtCompositionAux l c.blocks
#align list.split_wrt_composition List.splitWrtComposition

def compositionAsSetEquiv (n : ℕ) : CompositionAsSet n ≃ Finset (Fin (n - 1))
    where
  toFun c :=
    { i : Fin (n - 1) |
        (⟨1 + (i : ℕ), by
              apply (add_lt_add_left i.is_lt 1).trans_le
              rw [Nat.succ_eq_add_one, add_comm]
              exact add_le_add (Nat.sub_le n 1) (le_refl 1)⟩ :
            Fin n.succ) ∈
          c.boundaries }.toFinset
  invFun s :=
    { boundaries :=
        { i : Fin n.succ |
            i = 0 ∨ i = Fin.last n ∨ ∃ (j : Fin (n - 1)) (_hj : j ∈ s), (i : ℕ) = j + 1 }.toFinset
      zero_mem := by simp
      getLast_mem := by simp }
  left_inv := by
    intro c
    ext i
    simp only [add_comm, Set.toFinset_setOf, Finset.mem_univ,
     forall_true_left, Finset.mem_filter, true_and, exists_prop]
    constructor
    · rintro (rfl | rfl | ⟨j, hj1, hj2⟩)
      · exact c.zero_mem
      · exact c.getLast_mem
      · convert hj1
    · simp only [or_iff_not_imp_left]
      intro i_mem i_ne_zero i_ne_last
      simp? [Fin.ext_iff] at i_ne_zero i_ne_last says
        simp only [Fin.ext_iff, Fin.val_zero, Fin.val_last] at i_ne_zero i_ne_last
      have A : (1 + (i - 1) : ℕ) = (i : ℕ) := by
        rw [add_comm]
        exact Nat.succ_pred_eq_of_pos (pos_iff_ne_zero.mpr i_ne_zero)
      refine' ⟨⟨i - 1, _⟩, _, _⟩
      · have : (i : ℕ) < n + 1 := i.2
        simp? [Nat.lt_succ_iff_lt_or_eq, i_ne_last] at this says
          simp only [Nat.lt_succ_iff_lt_or_eq, i_ne_last, or_false] at this
        exact Nat.pred_lt_pred i_ne_zero this
      · convert i_mem
        simp only [ge_iff_le]
        rwa [add_comm]
      · simp only [ge_iff_le]
        symm
        rwa [add_comm]
  right_inv := by
    intro s
    ext i
    have : 1 + (i : ℕ) ≠ n := by
      apply ne_of_lt
      convert add_lt_add_left i.is_lt 1
      rw [add_comm]
      apply (Nat.succ_pred_eq_of_pos _).symm
      exact (zero_le i.val).trans_lt (i.2.trans_le (Nat.sub_le n 1))
    simp only [add_comm, Fin.ext_iff, Fin.val_zero, Fin.val_last, exists_prop, Set.toFinset_setOf,
      Finset.mem_univ, forall_true_left, Finset.mem_filter, add_eq_zero_iff, and_false,
      add_left_inj, false_or, true_and]
    erw [Set.mem_setOf_eq]
    simp [this, false_or_iff, add_right_inj, add_eq_zero_iff, one_ne_zero, false_and_iff,
      Fin.val_mk]
    constructor
    · intro h
      cases' h with n h
      · rw [add_comm] at this
        contradiction
      · cases' h with w h; cases' h with h₁ h₂
        rw [← Fin.ext_iff] at h₂
        rwa [h₂]
    · intro h
      apply Or.inr
      use i, h
#align composition_as_set_equiv compositionAsSetEquiv

def length : ℕ :=
  Finset.card c.boundaries - 1
#align composition_as_set.length CompositionAsSet.length

def boundary : Fin c.boundaries.card ↪o Fin (n + 1) :=
  c.boundaries.orderEmbOfFin rfl
#align composition_as_set.boundary CompositionAsSet.boundary

def blocksFun (i : Fin c.length) : ℕ :=
  c.boundary ⟨(i : ℕ) + 1, c.lt_length i⟩ - c.boundary ⟨i, c.lt_length' i⟩
#align composition_as_set.blocks_fun CompositionAsSet.blocksFun

def blocks (c : CompositionAsSet n) : List ℕ :=
  ofFn c.blocksFun
#align composition_as_set.blocks CompositionAsSet.blocks

def toComposition : Composition n where
  blocks := c.blocks
  blocks_pos := by simp only [blocks, forall_mem_ofFn_iff, blocksFun_pos c, forall_true_iff]
  blocks_sum := c.blocks_sum
#align composition_as_set.to_composition CompositionAsSet.toComposition

def compositionEquiv (n : ℕ) : Composition n ≃ CompositionAsSet n
    where
  toFun c := c.toCompositionAsSet
  invFun c := c.toComposition
  left_inv c := by
    ext1
    exact c.toCompositionAsSet_blocks
  right_inv c := by
    ext1
    exact c.toComposition_boundaries
#align composition_equiv compositionEquiv

structure made of a finset of `Fin (n+1)` called `c.boundaries`
and proofs that it contains `0` and `n`. (Taking a finset of `Fin n` containing `0` would not
make sense in the edge case `n = 0`, while the previous description works in all cases).
The elements of this set (other than `n`) correspond to leftmost points of blocks.
Thus, there is an equiv between `Composition n` and `CompositionAsSet n`. We
only construct basic API on `CompositionAsSet` (notably `c.length` and `c.blocks`) to be able
to construct this equiv, called `compositionEquiv n`. Since there is a straightforward equiv
between `CompositionAsSet n` and finsets of `{1, ..., n-1}` (obtained by removing `0` and `n`
from a `CompositionAsSet` and called `compositionAsSetEquiv n`), we deduce that
`CompositionAsSet n` and `Composition n` are both fintypes of cardinality `2^(n - 1)`
(see `compositionAsSet_card` and `composition_card`).

## Implementation details

structure and its API is in the construction of the composition of
formal multilinear series, and the proof that the composition of analytic functions is analytic.

The representation of a composition as a list is very handy as lists are very flexible and already
have a well-developed API.

## Tags

structure Composition (n : ℕ) where
  /-- List of positive integers summing to `n`-/
  blocks : List ℕ
  /-- Proof of positivity for `blocks`-/
  blocks_pos : ∀ {i}, i ∈ blocks → 0 < i
  /-- Proof that `blocks` sums to `n`-/
  blocks_sum : blocks.sum = n
#align composition Composition

structure
`CompositionAsSet n`. -/
@[ext]
structure CompositionAsSet (n : ℕ) where
  /-- Combinatorial viewpoint on a composition of `n` as consecutive integers `{0, ..., n-1}`-/
  boundaries : Finset (Fin n.succ)
  /-- Proof that `0` is a member of `boundaries`-/
  zero_mem : (0 : Fin n.succ) ∈ boundaries
  /-- Last element of the composition-/
  getLast_mem : Fin.last n ∈ boundaries
#align composition_as_set CompositionAsSet