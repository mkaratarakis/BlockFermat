def toSet (I : Box ι) : Set (ι → ℝ) := { x | x ∈ I }

instance : CoeTC (Box ι) (Set <| ι → ℝ) :=
  ⟨toSet⟩

@[simp]
theorem mem_mk {l u x : ι → ℝ} {H} : x ∈ mk l u H ↔ ∀ i, x i ∈ Ioc (l i) (u i) := Iff.rfl
#align box_integral.box.mem_mk BoxIntegral.Box.mem_mk

def : x ∈ I ↔ ∀ i, x i ∈ Ioc (I.lower i) (I.upper i) := Iff.rfl
#align box_integral.box.mem_def BoxIntegral.Box.mem_def

def : I ≤ J ↔ ∀ x ∈ I, x ∈ J := Iff.rfl
#align box_integral.box.le_def BoxIntegral.Box.le_def

def Icc : Box ι ↪o Set (ι → ℝ) :=
  OrderEmbedding.ofMapLEIff (fun I : Box ι ↦ Icc I.lower I.upper) fun I J ↦ (le_TFAE I J).out 2 0
#align box_integral.box.Icc BoxIntegral.Box.Icc

def : Box.Icc I = Icc I.lower I.upper := rfl
#align box_integral.box.Icc_def BoxIntegral.Box.Icc_def

def withBotToSet (o : WithBot (Box ι)) : Set (ι → ℝ) := o.elim ∅ (↑)

instance withBotCoe : CoeTC (WithBot (Box ι)) (Set (ι → ℝ)) :=
  ⟨withBotToSet⟩
#align box_integral.box.with_bot_coe BoxIntegral.Box.withBotCoe

def mk' (l u : ι → ℝ) : WithBot (Box ι) :=
  if h : ∀ i, l i < u i then ↑(⟨l, u, h⟩ : Box ι) else ⊥
#align box_integral.box.mk' BoxIntegral.Box.mk'

def face {n} (I : Box (Fin (n + 1))) (i : Fin (n + 1)) : Box (Fin n) :=
  ⟨I.lower ∘ Fin.succAbove i, I.upper ∘ Fin.succAbove i, fun _ ↦ I.lower_lt_upper _⟩
#align box_integral.box.face BoxIntegral.Box.face

def Ioo : Box ι →o Set (ι → ℝ) where
  toFun I := pi univ fun i ↦ Ioo (I.lower i) (I.upper i)
  monotone' _ _ h :=
    pi_mono fun i _ ↦ Ioo_subset_Ioo ((le_iff_bounds.1 h).1 i) ((le_iff_bounds.1 h).2 i)
#align box_integral.box.Ioo BoxIntegral.Box.Ioo

def distortion (I : Box ι) : ℝ≥0 :=
  Finset.univ.sup fun i : ι ↦ nndist I.lower I.upper / nndist (I.lower i) (I.upper i)
#align box_integral.box.distortion BoxIntegral.Box.distortion

structure `BoxIntegral.Box` both for ambient boxes and for elements of a partition.
Each box is stored as two points `lower upper : ι → ℝ` and a proof of `∀ i, lower i < upper i`. We
define instances `Membership (ι → ℝ) (Box ι)` and `CoeTC (Box ι) (Set <| ι → ℝ)` so that each box is
interpreted as the set `{x | ∀ i, x i ∈ Set.Ioc (I.lower i) (I.upper i)}`. This way boxes of a
partition are pairwise disjoint and their union is exactly the original box.

We require boxes to be nonempty, because this way coercion to sets is injective. The empty box can
be represented as `⊥ : WithBot (BoxIntegral.Box ι)`.

We define the following operations on boxes:

* coercion to `Set (ι → ℝ)` and `Membership (ι → ℝ) (BoxIntegral.Box ι)` as described above;
* `PartialOrder` and `SemilatticeSup` instances such that `I ≤ J` is equivalent to
  `(I : Set (ι → ℝ)) ⊆ J`;
* `Lattice` instances on `WithBot (BoxIntegral.Box ι)`;
* `BoxIntegral.Box.Icc`: the closed box `Set.Icc I.lower I.upper`; defined as a bundled monotone
  map from `Box ι` to `Set (ι → ℝ)`;
* `BoxIntegral.Box.face I i : Box (Fin n)`: a hyperface of `I : BoxIntegral.Box (Fin (n + 1))`;
* `BoxIntegral.Box.distortion`: the maximal ratio of two lengths of edges of a box; defined as the
  supremum of `nndist I.lower I.upper / nndist (I.lower i) (I.upper i)`.

We also provide a convenience constructor `BoxIntegral.Box.mk' (l u : ι → ℝ) : WithBot (Box ι)`
that returns the box `⟨l, u, _⟩` if it is nonempty and `⊥` otherwise.

## Tags

structure Box (ι : Type*) where
  (lower upper : ι → ℝ)
  lower_lt_upper : ∀ i, lower i < upper i
#align box_integral.box BoxIntegral.Box