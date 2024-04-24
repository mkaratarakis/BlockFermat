def toContinuousMap (f : ContinuousMonoidHom A B) : C(A, B) :=
  { f with }
#align continuous_monoid_hom.to_continuous_map ContinuousMonoidHom.toContinuousMap

def mk' (f : A →* B) (hf : Continuous f) : ContinuousMonoidHom A B :=
  { f with continuous_toFun := (hf : Continuous f.toFun)}
#align continuous_monoid_hom.mk' ContinuousMonoidHom.mk'

def comp (g : ContinuousMonoidHom B C) (f : ContinuousMonoidHom A B) : ContinuousMonoidHom A C :=
  mk' (g.toMonoidHom.comp f.toMonoidHom) (g.continuous_toFun.comp f.continuous_toFun)
#align continuous_monoid_hom.comp ContinuousMonoidHom.comp

def prod (f : ContinuousMonoidHom A B) (g : ContinuousMonoidHom A C) :
    ContinuousMonoidHom A (B × C) :=
  mk' (f.toMonoidHom.prod g.toMonoidHom) (f.continuous_toFun.prod_mk g.continuous_toFun)
#align continuous_monoid_hom.prod ContinuousMonoidHom.prod

def prod_map (f : ContinuousMonoidHom A C) (g : ContinuousMonoidHom B D) :
    ContinuousMonoidHom (A × B) (C × D) :=
  mk' (f.toMonoidHom.prodMap g.toMonoidHom) (f.continuous_toFun.prod_map g.continuous_toFun)
#align continuous_monoid_hom.prod_map ContinuousMonoidHom.prod_map

def one : ContinuousMonoidHom A B :=
  mk' 1 continuous_const
#align continuous_monoid_hom.one ContinuousMonoidHom.one

def id : ContinuousMonoidHom A A :=
  mk' (MonoidHom.id A) continuous_id
#align continuous_monoid_hom.id ContinuousMonoidHom.id

def fst : ContinuousMonoidHom (A × B) A :=
  mk' (MonoidHom.fst A B) continuous_fst
#align continuous_monoid_hom.fst ContinuousMonoidHom.fst

def snd : ContinuousMonoidHom (A × B) B :=
  mk' (MonoidHom.snd A B) continuous_snd
#align continuous_monoid_hom.snd ContinuousMonoidHom.snd

def inl : ContinuousMonoidHom A (A × B) :=
  prod (id A) (one A B)
#align continuous_monoid_hom.inl ContinuousMonoidHom.inl

def inr : ContinuousMonoidHom B (A × B) :=
  prod (one B A) (id B)
#align continuous_monoid_hom.inr ContinuousMonoidHom.inr

def diag : ContinuousMonoidHom A (A × A) :=
  prod (id A) (id A)
#align continuous_monoid_hom.diag ContinuousMonoidHom.diag

def swap : ContinuousMonoidHom (A × B) (B × A) :=
  prod (snd A B) (fst A B)
#align continuous_monoid_hom.swap ContinuousMonoidHom.swap

def mul : ContinuousMonoidHom (E × E) E :=
  mk' mulMonoidHom continuous_mul
#align continuous_monoid_hom.mul ContinuousMonoidHom.mul

def inv : ContinuousMonoidHom E E :=
  mk' invMonoidHom continuous_inv
#align continuous_monoid_hom.inv ContinuousMonoidHom.inv

def coprod (f : ContinuousMonoidHom A E) (g : ContinuousMonoidHom B E) :
    ContinuousMonoidHom (A × B) E :=
  (mul E).comp (f.prod_map g)
#align continuous_monoid_hom.coprod ContinuousMonoidHom.coprod

def compLeft (f : ContinuousMonoidHom A B) :
    ContinuousMonoidHom (ContinuousMonoidHom B E) (ContinuousMonoidHom A E) where
  toFun g := g.comp f
  map_one' := rfl
  map_mul' _g _h := rfl
  continuous_toFun := f.continuous_comp_left
#align continuous_monoid_hom.comp_left ContinuousMonoidHom.compLeft

def compRight {B : Type*} [CommGroup B] [TopologicalSpace B] [TopologicalGroup B]
    (f : ContinuousMonoidHom B E) :
    ContinuousMonoidHom (ContinuousMonoidHom A B) (ContinuousMonoidHom A E) where
  toFun g := f.comp g
  map_one' := ext fun _a => map_one f
  map_mul' g h := ext fun a => map_mul f (g a) (h a)
  continuous_toFun := f.continuous_comp_right
#align continuous_monoid_hom.comp_right ContinuousMonoidHom.compRight

structure ContinuousAddMonoidHom (A B : Type*) [AddMonoid A] [AddMonoid B] [TopologicalSpace A]
  [TopologicalSpace B] extends A →+ B where
  /-- Proof of continuity of the Hom. -/
  continuous_toFun : @Continuous A B _ _ toFun
#align continuous_add_monoid_hom ContinuousAddMonoidHom

structure ContinuousMonoidHom extends A →* B where
  /-- Proof of continuity of the Hom. -/
  continuous_toFun : @Continuous A B _ _ toFun
#align continuous_monoid_hom ContinuousMonoidHom