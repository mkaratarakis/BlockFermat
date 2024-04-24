def LiftPropWithinAt (P : (H → H') → Set H → H → Prop) (f : M → M') (s : Set M) (x : M) : Prop :=
  ContinuousWithinAt f s x ∧
    P (chartAt H' (f x) ∘ f ∘ (chartAt H x).symm) ((chartAt H x).symm ⁻¹' s) (chartAt H x x)
#align charted_space.lift_prop_within_at ChartedSpace.LiftPropWithinAt

def LiftPropOn (P : (H → H') → Set H → H → Prop) (f : M → M') (s : Set M) :=
  ∀ x ∈ s, LiftPropWithinAt P f s x
#align charted_space.lift_prop_on ChartedSpace.LiftPropOn

def LiftPropAt (P : (H → H') → Set H → H → Prop) (f : M → M') (x : M) :=
  LiftPropWithinAt P f univ x
#align charted_space.lift_prop_at ChartedSpace.LiftPropAt

def LiftProp (P : (H → H') → Set H → H → Prop) (f : M → M') :=
  ∀ x, LiftPropAt P f x
#align charted_space.lift_prop ChartedSpace.LiftProp

def IsLocalStructomorphWithinAt (f : H → H) (s : Set H) (x : H) : Prop :=
  x ∈ s → ∃ e : PartialHomeomorph H H, e ∈ G ∧ EqOn f e.toFun (s ∩ e.source) ∧ x ∈ e.source
#align structure_groupoid.is_local_structomorph_within_at StructureGroupoid.IsLocalStructomorphWithinAt

structure LocalInvariantProp (P : (H → H') → Set H → H → Prop) : Prop where
  is_local : ∀ {s x u} {f : H → H'}, IsOpen u → x ∈ u → (P f s x ↔ P f (s ∩ u) x)
  right_invariance' : ∀ {s x f} {e : PartialHomeomorph H H},
    e ∈ G → x ∈ e.source → P f s x → P (f ∘ e.symm) (e.symm ⁻¹' s) (e x)
  congr_of_forall : ∀ {s x} {f g : H → H'}, (∀ y ∈ s, f y = g y) → f x = g x → P f s x → P g s x
  left_invariance' : ∀ {s x f} {e' : PartialHomeomorph H' H'},
    e' ∈ G' → s ⊆ f ⁻¹' e'.source → f x ∈ e'.source → P f s x → P (e' ∘ f) s x
#align structure_groupoid.local_invariant_prop StructureGroupoid.LocalInvariantProp

structure groupoid (by composition in the source space and in the target space), then
expressing it in charted spaces does not depend on the element of the maximal atlas one uses
both in the source and in the target manifolds, provided they are defined around `x` and `g x`
respectively, and provided `g` is continuous within `s` at `x` (otherwise, the local behavior
of `g` at `x` can not be captured with a chart in the target). -/
theorem liftPropWithinAt_indep_chart_aux (he : e ∈ G.maximalAtlas M) (xe : x ∈ e.source)
    (he' : e' ∈ G.maximalAtlas M) (xe' : x ∈ e'.source) (hf : f ∈ G'.maximalAtlas M')
    (xf : g x ∈ f.source) (hf' : f' ∈ G'.maximalAtlas M') (xf' : g x ∈ f'.source)
    (hgs : ContinuousWithinAt g s x) :
    P (f ∘ g ∘ e.symm) (e.symm ⁻¹' s) (e x) ↔ P (f' ∘ g ∘ e'.symm) (e'.symm ⁻¹' s) (e' x) := by
  rw [← Function.comp.assoc, hG.liftPropWithinAt_indep_chart_source_aux (f ∘ g) he xe he' xe',
    Function.comp.assoc, hG.liftPropWithinAt_indep_chart_target_aux xe' hf xf hf' xf' hgs]
#align structure_groupoid.local_invariant_prop.lift_prop_within_at_indep_chart_aux StructureGroupoid.LocalInvariantProp.liftPropWithinAt_indep_chart_aux

structure groupoid `G` for `H`, relative to a set `s` in `H`, if for all points `x` in the set, the
function agrees with a `G`-structomorphism on `s` in a neighbourhood of `x`. -/
def IsLocalStructomorphWithinAt (f : H → H) (s : Set H) (x : H) : Prop :=
  x ∈ s → ∃ e : PartialHomeomorph H H, e ∈ G ∧ EqOn f e.toFun (s ∩ e.source) ∧ x ∈ e.source
#align structure_groupoid.is_local_structomorph_within_at StructureGroupoid.IsLocalStructomorphWithinAt