def Simps.coe (U : Opens α) : Set α := U
#align topological_space.opens.simps.coe TopologicalSpace.Opens.Simps.coe

def interior (s : Set α) : Opens α :=
  ⟨interior s, isOpen_interior⟩
#align topological_space.opens.interior TopologicalSpace.Opens.interior

def gi : GaloisCoinsertion (↑) (@interior α _) where
  choice s hs := ⟨s, interior_eq_iff_isOpen.mp <| le_antisymm interior_subset hs⟩
  gc := gc
  u_l_le _ := interior_subset
  choice_eq _s hs := le_antisymm hs interior_subset
#align topological_space.opens.gi TopologicalSpace.Opens.gi

def {ι} (s : ι → Opens α) : ⨆ i, s i = ⟨⋃ i, s i, isOpen_iUnion fun i => (s i).2⟩ :=
  ext <| coe_iSup s
#align topological_space.opens.supr_def TopologicalSpace.Opens.iSup_def

def _
#align topological_space.opens.supr_mk TopologicalSpace.Opens.iSup_mk

def IsBasis (B : Set (Opens α)) : Prop :=
  IsTopologicalBasis (((↑) : _ → Set α) '' B)
#align topological_space.opens.is_basis TopologicalSpace.Opens.IsBasis

def comap (f : C(α, β)) : FrameHom (Opens β) (Opens α) where
  toFun s := ⟨f ⁻¹' s, s.2.preimage f.continuous⟩
  map_sSup' s := ext <| by simp only [coe_sSup, preimage_iUnion, biUnion_image, coe_mk]
  map_inf' a b := rfl
  map_top' := rfl
#align topological_space.opens.comap TopologicalSpace.Opens.comap

def _root_.Homeomorph.opensCongr (f : α ≃ₜ β) : Opens α ≃o Opens β where
  toFun := Opens.comap f.symm.toContinuousMap
  invFun := Opens.comap f.toContinuousMap
  left_inv := fun U => ext <| f.toEquiv.preimage_symm_preimage _
  right_inv := fun U => ext <| f.toEquiv.symm_preimage_preimage _
  map_rel_iff' := by
    simp only [← SetLike.coe_subset_coe]; exact f.symm.surjective.preimage_subset_preimage_iff
#align homeomorph.opens_congr Homeomorph.opensCongr

def comap (f : C(α, β)) (x : α) : LatticeHom (OpenNhdsOf (f x)) (OpenNhdsOf x) where
  toFun U := ⟨Opens.comap f U.1, U.mem⟩
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl
#align topological_space.open_nhds_of.comap TopologicalSpace.OpenNhdsOf.comap

def opens_find_tac : expr → Option auto_cases_tac
--   | q(TopologicalSpace.Opens _) => tac_cases
--   | _ => none
-- #align tactic.auto_cases.opens_find_tac tactic.auto_cases.opens_find_tac

def auto_cases_opens : tactic String :=
--   auto_cases tactic.auto_cases.opens_find_tac
-- #align tactic.auto_cases_opens tactic.auto_cases_opens

structure Opens where
  /-- The underlying set of a bundled `TopologicalSpace.Opens` object. -/
  carrier : Set α
  /-- The `TopologicalSpace.Opens.carrier _` is an open set. -/
  is_open' : IsOpen carrier
#align topological_space.opens TopologicalSpace.Opens

structure OpenNhdsOf (x : α) extends Opens α where
  /-- The point `x` belongs to every `U : TopologicalSpace.OpenNhdsOf x`. -/
  mem' : x ∈ carrier
#align topological_space.open_nhds_of TopologicalSpace.OpenNhdsOf