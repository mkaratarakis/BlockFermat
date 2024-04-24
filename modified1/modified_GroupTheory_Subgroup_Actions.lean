def (g : S) (m : α) : g • m = (g : G) • m := rfl
#align subgroup.smul_def Subgroup.smul_def

def AddSubgroup.vadd_def

@[to_additive (attr := simp)]
lemma mk_smul (g : G) (hg : g ∈ S) (a : α) : (⟨g, hg⟩ : S) • a = g • a := rfl

end MulAction

@[to_additive]
instance smulCommClass_left [MulAction G β] [SMul α β] [SMulCommClass G α β] (S : Subgroup G) :
    SMulCommClass S α β :=
  S.toSubmonoid.smulCommClass_left
#align subgroup.smul_comm_class_left Subgroup.smulCommClass_left