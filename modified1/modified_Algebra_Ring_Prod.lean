def fst : R × S →ₙ+* R :=
  { MulHom.fst R S, AddMonoidHom.fst R S with toFun := Prod.fst }
#align non_unital_ring_hom.fst NonUnitalRingHom.fst

def snd : R × S →ₙ+* S :=
  { MulHom.snd R S, AddMonoidHom.snd R S with toFun := Prod.snd }
#align non_unital_ring_hom.snd NonUnitalRingHom.snd

def prod (f : R →ₙ+* S) (g : R →ₙ+* T) : R →ₙ+* S × T :=
  { MulHom.prod (f : MulHom R S) (g : MulHom R T), AddMonoidHom.prod (f : R →+ S) (g : R →+ T) with
    toFun := fun x => (f x, g x) }
#align non_unital_ring_hom.prod NonUnitalRingHom.prod

def prodMap : R × S →ₙ+* R' × S' :=
  (f.comp (fst R S)).prod (g.comp (snd R S))
#align non_unital_ring_hom.prod_map NonUnitalRingHom.prodMap

def : prodMap f g = (f.comp (fst R S)).prod (g.comp (snd R S)) :=
  rfl
#align non_unital_ring_hom.prod_map_def NonUnitalRingHom.prodMap_def

def fst : R × S →+* R :=
  { MonoidHom.fst R S, AddMonoidHom.fst R S with toFun := Prod.fst }
#align ring_hom.fst RingHom.fst

def snd : R × S →+* S :=
  { MonoidHom.snd R S, AddMonoidHom.snd R S with toFun := Prod.snd }
#align ring_hom.snd RingHom.snd

def prod (f : R →+* S) (g : R →+* T) : R →+* S × T :=
  { MonoidHom.prod (f : R →* S) (g : R →* T), AddMonoidHom.prod (f : R →+ S) (g : R →+ T) with
    toFun := fun x => (f x, g x) }
#align ring_hom.prod RingHom.prod

def prodMap : R × S →+* R' × S' :=
  (f.comp (fst R S)).prod (g.comp (snd R S))
#align ring_hom.prod_map RingHom.prodMap

def : prodMap f g = (f.comp (fst R S)).prod (g.comp (snd R S)) :=
  rfl
#align ring_hom.prod_map_def RingHom.prodMap_def

def prodComm : R × S ≃+* S × R :=
  { AddEquiv.prodComm, MulEquiv.prodComm with }
#align ring_equiv.prod_comm RingEquiv.prodComm

def prodProdProdComm : (R × R') × S × S' ≃+* (R × S) × R' × S' :=
  { AddEquiv.prodProdProdComm R R' S S', MulEquiv.prodProdProdComm R R' S S' with
    toFun := fun rrss => ((rrss.1.1, rrss.2.1), (rrss.1.2, rrss.2.2))
    invFun := fun rsrs => ((rsrs.1.1, rsrs.2.1), (rsrs.1.2, rsrs.2.2)) }
#align ring_equiv.prod_prod_prod_comm RingEquiv.prodProdProdComm

def prodZeroRing : R ≃+* R × S where
  toFun x := (x, 0)
  invFun := Prod.fst
  map_add' := by simp
  map_mul' := by simp
  left_inv x := rfl
  right_inv x := by cases x; simp [eq_iff_true_of_subsingleton]
#align ring_equiv.prod_zero_ring RingEquiv.prodZeroRing

def zeroRingProd : R ≃+* S × R where
  toFun x := (0, x)
  invFun := Prod.snd
  map_add' := by simp
  map_mul' := by simp
  left_inv x := rfl
  right_inv x := by cases x; simp [eq_iff_true_of_subsingleton]
#align ring_equiv.zero_ring_prod RingEquiv.zeroRingProd