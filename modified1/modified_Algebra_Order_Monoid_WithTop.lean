def addHom : α →+ WithTop α where
  toFun := WithTop.some
  map_zero' := rfl
  map_add' _ _ := rfl
#align with_top.coe_add_hom WithTop.addHom

def _root_.OneHom.withTopMap {M N : Type*} [One M] [One N] (f : OneHom M N) :
    OneHom (WithTop M) (WithTop N) where
  toFun := WithTop.map f
  map_one' := by rw [WithTop.map_one, map_one, coe_one]
#align one_hom.with_top_map OneHom.withTopMap

def _root_.AddHom.withTopMap {M N : Type*} [Add M] [Add N] (f : AddHom M N) :
    AddHom (WithTop M) (WithTop N) where
  toFun := WithTop.map f
  map_add' := WithTop.map_add f
#align add_hom.with_top_map AddHom.withTopMap

def _root_.AddMonoidHom.withTopMap {M N : Type*} [AddZeroClass M] [AddZeroClass N]
    (f : M →+ N) : WithTop M →+ WithTop N :=
  { ZeroHom.withTopMap f.toZeroHom, AddHom.withTopMap f.toAddHom with toFun := WithTop.map f }
#align add_monoid_hom.with_top_map AddMonoidHom.withTopMap

def addHom : α →+ WithBot α where
  toFun := WithTop.some
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp, norm_cast] lemma coe_addHom : ⇑(addHom : α →+ WithBot α) = WithBot.some := rfl

@[simp, norm_cast]
lemma coe_nsmul (a : α) (n : ℕ) : ↑(n • a) = n • (a : WithBot α) :=
  (addHom : α →+ WithBot α).map_nsmul _ _
#align with_bot.coe_nsmul WithBot.coe_nsmul

def _root_.OneHom.withBotMap {M N : Type*} [One M] [One N] (f : OneHom M N) :
    OneHom (WithBot M) (WithBot N) where
  toFun := WithBot.map f
  map_one' := by rw [WithBot.map_one, map_one, coe_one]
#align one_hom.with_bot_map OneHom.withBotMap

def _root_.AddHom.withBotMap {M N : Type*} [Add M] [Add N] (f : AddHom M N) :
    AddHom (WithBot M) (WithBot N) where
  toFun := WithBot.map f
  map_add' := WithBot.map_add f
#align add_hom.with_bot_map AddHom.withBotMap

def _root_.AddMonoidHom.withBotMap {M N : Type*} [AddZeroClass M] [AddZeroClass N]
    (f : M →+ N) : WithBot M →+ WithBot N :=
  { ZeroHom.withBotMap f.toZeroHom, AddHom.withBotMap f.toAddHom with toFun := WithBot.map f }
#align add_monoid_hom.with_bot_map AddMonoidHom.withBotMap