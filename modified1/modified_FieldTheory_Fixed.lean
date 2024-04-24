def FixedBy.subfield : Subfield F where
  carrier := fixedBy F m
  zero_mem' := smul_zero m
  add_mem' hx hy := (smul_add m _ _).trans <| congr_arg₂ _ hx hy
  neg_mem' hx := (smul_neg m _).trans <| congr_arg _ hx
  one_mem' := smul_one m
  mul_mem' hx hy := (smul_mul' m _ _).trans <| congr_arg₂ _ hx hy
  inv_mem' x hx := (smul_inv'' m x).trans <| congr_arg _ hx
#align fixed_by.subfield FixedBy.subfield

def subfield : Subfield F :=
  Subfield.copy (⨅ m : M, FixedBy.subfield F m) (fixedPoints M F)
    (by ext z; simp [fixedPoints, FixedBy.subfield, iInf, Subfield.mem_sInf]; rfl)
#align fixed_points.subfield FixedPoints.subfield

def minpoly : Polynomial (FixedPoints.subfield G F) :=
  (prodXSubSMul G F x).toSubring (FixedPoints.subfield G F).toSubring fun _ hc g =>
    let ⟨n, _, hn⟩ := Polynomial.mem_frange_iff.1 hc
    hn.symm ▸ prodXSubSMul.coeff G F x g n
#align fixed_points.minpoly FixedPoints.minpoly

def toAlgHomEquiv (G : Type u) (F : Type v) [Group G] [Field F] [Finite G] [MulSemiringAction G F]
    [FaithfulSMul G F] : G ≃ (F →ₐ[FixedPoints.subfield G F] F) :=
  Equiv.ofBijective _ (toAlgHom_bijective G F)
#align fixed_points.to_alg_hom_equiv FixedPoints.toAlgHomEquiv