def IsCyclic.commGroup [hg : Group α] [IsCyclic α] : CommGroup α :=
  { hg with
    mul_comm := fun x y =>
      let ⟨_, hg⟩ := IsCyclic.exists_generator (α := α)
      let ⟨_, hn⟩ := hg x
      let ⟨_, hm⟩ := hg y
      hm ▸ hn ▸ zpow_mul_comm _ _ _ }
#align is_cyclic.comm_group IsCyclic.commGroup

def commGroupOfCycleCenterQuotient [IsCyclic H] (f : G →* H) (hf : f.ker ≤ center G) :
    CommGroup G :=
  { show Group G by infer_instance with mul_comm := commutative_of_cyclic_center_quotient f hf }
#align comm_group_of_cycle_center_quotient commGroupOfCycleCenterQuotient