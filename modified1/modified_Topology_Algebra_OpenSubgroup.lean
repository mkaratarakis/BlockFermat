def toOpens (U : OpenSubgroup G) : Opens G := ⟨U, U.isOpen'⟩

@[to_additive]
instance hasCoeOpens : CoeTC (OpenSubgroup G) (Opens G) := ⟨toOpens⟩
#align open_subgroup.has_coe_opens OpenSubgroup.hasCoeOpens

def prod (U : OpenSubgroup G) (V : OpenSubgroup H) : OpenSubgroup (G × H) :=
  ⟨.prod U V, U.isOpen.prod V.isOpen⟩
#align open_subgroup.prod OpenSubgroup.prod

def comap (f : G →* N) (hf : Continuous f) (H : OpenSubgroup N) : OpenSubgroup G :=
  ⟨.comap f H, H.isOpen.preimage hf⟩
#align open_subgroup.comap OpenSubgroup.comap

structure OpenAddSubgroup (G : Type*) [AddGroup G] [TopologicalSpace G] extends AddSubgroup G where
  isOpen' : IsOpen carrier
#align open_add_subgroup OpenAddSubgroup

structure OpenSubgroup (G : Type*) [Group G] [TopologicalSpace G] extends Subgroup G where
  isOpen' : IsOpen carrier
#align open_subgroup OpenSubgroup