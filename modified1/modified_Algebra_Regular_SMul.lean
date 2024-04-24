def IsSMulRegular [SMul R M] (c : R) :=
  Function.Injective ((c • ·) : M → M)
#align is_smul_regular IsSMulRegular