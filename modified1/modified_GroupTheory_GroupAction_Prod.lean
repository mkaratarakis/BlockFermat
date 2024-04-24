def (a : M) (x : α × β) : a • x = (a • x.1, a • x.2) :=
  rfl
#align prod.smul_def Prod.smul_def

def Prod.vadd_def

@[to_additive (attr := simp)]
theorem smul_swap : (a • x).swap = a • x.swap :=
  rfl
#align prod.smul_swap Prod.smul_swap

def (p : α × β) (c : E) : p ^ c = (p.1 ^ c, p.2 ^ c) :=
  rfl
#align prod.pow_def Prod.pow_def

def smulMulHom [Monoid α] [Mul β] [MulAction α β] [IsScalarTower α β β] [SMulCommClass α β β] :
    α × β →ₙ* β where
  toFun a := a.1 • a.2
  map_mul' _ _ := (smul_mul_smul _ _ _ _).symm
#align smul_mul_hom smulMulHom

def smulMonoidHom [Monoid α] [MulOneClass β] [MulAction α β] [IsScalarTower α β β]
    [SMulCommClass α β β] : α × β →* β :=
  { smulMulHom with map_one' := one_smul _ _ }
#align smul_monoid_hom smulMonoidHom