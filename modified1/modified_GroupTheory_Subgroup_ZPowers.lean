def zpowers (g : G) : Subgroup G :=
  Subgroup.copy (zpowersHom G g).range (Set.range (g ^ · : ℤ → G)) rfl
#align subgroup.zpowers Subgroup.zpowers

def zmultiples (a : A) : AddSubgroup A :=
  AddSubgroup.copy (zmultiplesHom A a).range (Set.range ((· • a) : ℤ → A)) rfl
#align add_subgroup.zmultiples AddSubgroup.zmultiples