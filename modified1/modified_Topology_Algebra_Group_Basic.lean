def Homeomorph.mulLeft (a : G) : G ≃ₜ G :=
  { Equiv.mulLeft a with
    continuous_toFun := continuous_const.mul continuous_id
    continuous_invFun := continuous_const.mul continuous_id }
#align homeomorph.mul_left Homeomorph.mulLeft

def Homeomorph.mulRight (a : G) : G ≃ₜ G :=
  { Equiv.mulRight a with
    continuous_toFun := continuous_id.mul continuous_const
    continuous_invFun := continuous_id.mul continuous_const }
#align homeomorph.mul_right Homeomorph.mulRight

def Homeomorph.inv (G : Type*) [TopologicalSpace G] [InvolutiveInv G]
    [ContinuousInv G] : G ≃ₜ G :=
  { Equiv.inv G with
    continuous_toFun := continuous_inv
    continuous_invFun := continuous_inv }
#align homeomorph.inv Homeomorph.inv

def Homeomorph.shearMulRight : G × G ≃ₜ G × G :=
  { Equiv.prodShear (Equiv.refl _) Equiv.mulLeft with
    continuous_toFun := continuous_fst.prod_mk continuous_mul
    continuous_invFun := continuous_fst.prod_mk <| continuous_fst.inv.mul continuous_snd }
#align homeomorph.shear_mul_right Homeomorph.shearMulRight

def Subgroup.topologicalClosure (s : Subgroup G) : Subgroup G :=
  { s.toSubmonoid.topologicalClosure with
    carrier := _root_.closure (s : Set G)
    inv_mem' := fun {g} hg => by simpa only [← Set.mem_inv, inv_closure, inv_coe_set] using hg }
#align subgroup.topological_closure Subgroup.topologicalClosure

def Subgroup.connectedComponentOfOne (G : Type*) [TopologicalSpace G] [Group G]
    [TopologicalGroup G] : Subgroup G where
  carrier := connectedComponent (1 : G)
  one_mem' := mem_connectedComponent
  mul_mem' hg hh := mul_mem_connectedComponent_one hg hh
  inv_mem' hg := inv_mem_connectedComponent_one hg
#align subgroup.connected_component_of_one Subgroup.connectedComponentOfOne

def Subgroup.commGroupTopologicalClosure [T2Space G] (s : Subgroup G)
    (hs : ∀ x y : s, x * y = y * x) : CommGroup s.topologicalClosure :=
  { s.topologicalClosure.toGroup, s.toSubmonoid.commMonoidTopologicalClosure hs with }
#align subgroup.comm_group_topological_closure Subgroup.commGroupTopologicalClosure

def Homeomorph.divLeft (x : G) : G ≃ₜ G :=
  { Equiv.divLeft x with
    continuous_toFun := continuous_const.div' continuous_id
    continuous_invFun := continuous_inv.mul continuous_const }
#align homeomorph.div_left Homeomorph.divLeft

def Homeomorph.divRight (x : G) : G ≃ₜ G :=
  { Equiv.divRight x with
    continuous_toFun := continuous_id.div' continuous_const
    continuous_invFun := continuous_id.mul continuous_const }
#align homeomorph.div_right Homeomorph.divRight

def nhdsMulHom : G →ₙ* Filter G where
  toFun := 𝓝
  map_mul' _ _ := nhds_mul _ _
#align nhds_mul_hom nhdsMulHom

def toUnits_homeomorph [Group G] [TopologicalSpace G] [ContinuousInv G] : G ≃ₜ Gˣ where
  toEquiv := toUnits.toEquiv
  continuous_toFun := Units.continuous_iff.2 ⟨continuous_id, continuous_inv⟩
  continuous_invFun := Units.continuous_val
#align to_units_homeomorph toUnits_homeomorph

def Homeomorph.prodUnits : (α × β)ˣ ≃ₜ αˣ × βˣ where
  continuous_toFun :=
    (continuous_fst.units_map (MonoidHom.fst α β)).prod_mk
      (continuous_snd.units_map (MonoidHom.snd α β))
  continuous_invFun :=
    Units.continuous_iff.2
      ⟨continuous_val.fst'.prod_mk continuous_val.snd',
        continuous_coe_inv.fst'.prod_mk continuous_coe_inv.snd'⟩
  toEquiv := MulEquiv.prodUnits.toEquiv
#align units.homeomorph.prod_units Units.Homeomorph.prodUnits

def coinduced {α β : Type*} [t : TopologicalSpace α] [Group β] (f : α → β) : GroupTopology β :=
  sInf { b : GroupTopology β | TopologicalSpace.coinduced f t ≤ b.toTopologicalSpace }
#align group_topology.coinduced GroupTopology.coinduced

structure GroupTopology (α : Type u) [Group α] extends TopologicalSpace α, TopologicalGroup α :
  Type u
#align group_topology GroupTopology

structure AddGroupTopology (α : Type u) [AddGroup α] extends TopologicalSpace α,
  TopologicalAddGroup α : Type u
#align add_group_topology AddGroupTopology