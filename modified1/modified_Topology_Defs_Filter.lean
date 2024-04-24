def nhds (x : X) : Filter X :=
  ⨅ s ∈ { s : Set X | x ∈ s ∧ IsOpen s }, 𝓟 s
#align nhds nhds

def nhds_def

@[inherit_doc]
scoped[Topology] notation "𝓝" => nhds

/-- The "neighborhood within" filter. Elements of `𝓝[s] x` are sets containing the
intersection of `s` and a neighborhood of `x`. -/
def nhdsWithin (x : X) (s : Set X) : Filter X :=
  𝓝 x ⊓ 𝓟 s
#align nhds_within nhdsWithin

def nhdsSet (s : Set X) : Filter X :=
  sSup (nhds '' s)
#align nhds_set nhdsSet

def ContinuousAt (f : X → Y) (x : X) :=
  Tendsto f (𝓝 x) (𝓝 (f x))
#align continuous_at ContinuousAt

def ContinuousWithinAt (f : X → Y) (s : Set X) (x : X) : Prop :=
  Tendsto f (𝓝[s] x) (𝓝 (f x))
#align continuous_within_at ContinuousWithinAt

def ContinuousOn (f : X → Y) (s : Set X) : Prop :=
  ∀ x ∈ s, ContinuousWithinAt f s x
#align continuous_on ContinuousOn

def Specializes (x y : X) : Prop := 𝓝 x ≤ 𝓝 y
#align specializes Specializes

def Inseparable (x y : X) : Prop :=
  𝓝 x = 𝓝 y
#align inseparable Inseparable

def specializationPreorder : Preorder X :=
  { Preorder.lift (OrderDual.toDual ∘ 𝓝) with
    le := fun x y => y ⤳ x
    lt := fun x y => y ⤳ x ∧ ¬x ⤳ y }
#align specialization_preorder specializationPreorder

def inseparableSetoid : Setoid X := { Setoid.comap 𝓝 ⊥ with r := Inseparable }
#align inseparable_setoid inseparableSetoid

def SeparationQuotient := Quotient (inseparableSetoid X)
#align separation_quotient SeparationQuotient

def lim [Nonempty X] (f : Filter X) : X :=
  Classical.epsilon fun x => f ≤ 𝓝 x
#align Lim lim

def Ultrafilter.lim (F : Ultrafilter X) : X :=
  @lim X _ (nonempty_of_neBot F) F
#align ultrafilter.Lim Ultrafilter.lim

def limUnder {α : Type*} [Nonempty X] (f : Filter α) (g : α → X) : X :=
  lim (f.map g)
#align lim limUnder

def ClusterPt (x : X) (F : Filter X) : Prop :=
  NeBot (𝓝 x ⊓ F)
#align cluster_pt ClusterPt

def MapClusterPt {ι : Type*} (x : X) (F : Filter ι) (u : ι → X) : Prop :=
  ClusterPt x (map u F)
#align map_cluster_pt MapClusterPt

def AccPt (x : X) (F : Filter X) : Prop :=
  NeBot (𝓝[≠] x ⊓ F)
#align acc_pt AccPt

def IsCompact (s : Set X) :=
  ∀ ⦃f⦄ [NeBot f], f ≤ 𝓟 s → ∃ x ∈ s, ClusterPt x f
#align is_compact IsCompact

def Filter.cocompact : Filter X :=
  ⨅ (s : Set X) (_ : IsCompact s), 𝓟 sᶜ
#align filter.cocompact Filter.cocompact

def Filter.coclosedCompact : Filter X :=
  ⨅ (s : Set X) (_ : IsClosed s) (_ : IsCompact s), 𝓟 sᶜ
#align filter.coclosed_compact Filter.coclosedCompact