def Submonoid.FG (P : Submonoid M) : Prop :=
  ∃ S : Finset M, Submonoid.closure ↑S = P
#align submonoid.fg Submonoid.FG

def : Monoid.FG M ↔ (⊤ : Submonoid M).FG :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩
#align monoid.fg_def Monoid.fg_def

def : AddMonoid.FG N ↔ (⊤ : AddSubmonoid N).FG :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩
#align add_monoid.fg_def AddMonoid.fg_def

def Subgroup.FG (P : Subgroup G) : Prop :=
  ∃ S : Finset G, Subgroup.closure ↑S = P
#align subgroup.fg Subgroup.FG

def : Group.FG G ↔ (⊤ : Subgroup G).FG :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩
#align group.fg_def Group.fg_def

def : AddGroup.FG H ↔ (⊤ : AddSubgroup H).FG :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩
#align add_group.fg_def AddGroup.fg_def

def Group.rank [h : Group.FG G] :=
  @Nat.find _ (Classical.decPred _) (Group.fg_iff'.mp h)
#align group.rank Group.rank