def prod : Ideal (R × S) where
  carrier := { x | x.fst ∈ I ∧ x.snd ∈ J }
  zero_mem' := by simp
  add_mem' := by
    rintro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ⟨ha₁, ha₂⟩ ⟨hb₁, hb₂⟩
    exact ⟨I.add_mem ha₁ hb₁, J.add_mem ha₂ hb₂⟩
  smul_mem' := by
    rintro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ⟨hb₁, hb₂⟩
    exact ⟨I.mul_mem_left _ hb₁, J.mul_mem_left _ hb₂⟩
#align ideal.prod Ideal.prod

def idealProdEquiv : Ideal (R × S) ≃ Ideal R × Ideal S
    where
  toFun I := ⟨map (RingHom.fst R S) I, map (RingHom.snd R S) I⟩
  invFun I := prod I.1 I.2
  left_inv I := (ideal_prod_eq I).symm
  right_inv := fun ⟨I, J⟩ => by simp
#align ideal.ideal_prod_equiv Ideal.idealProdEquiv