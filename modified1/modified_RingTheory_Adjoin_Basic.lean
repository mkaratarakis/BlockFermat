def adjoinCommSemiringOfComm {s : Set A} (hcomm : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a) :
    CommSemiring (adjoin R s) :=
  { (adjoin R s).toSemiring with
    mul_comm := fun x y => by
      ext
      simp only [Subalgebra.coe_mul]
      exact adjoin_induction₂ x.prop y.prop hcomm (fun _ _ => by rw [commutes])
        (fun r x _hx => commutes r x) (fun r x _hx => (commutes r x).symm)
        (fun _ _ _ h₁ h₂ => by simp only [add_mul, mul_add, h₁, h₂])
        (fun _ _ _ h₁ h₂ => by simp only [add_mul, mul_add, h₁, h₂])
        (fun x₁ x₂ y₁ h₁ h₂ => by rw [mul_assoc, h₂, ← mul_assoc y₁, ← h₁, mul_assoc x₁])
        fun x₁ x₂ y₁ h₁ h₂ => by rw [mul_assoc x₂, ← h₂, ← mul_assoc x₂, ← h₁, ← mul_assoc] }
#align algebra.adjoin_comm_semiring_of_comm Algebra.adjoinCommSemiringOfComm

def adjoinCommRingOfComm {s : Set A} (hcomm : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a) :
    CommRing (adjoin R s) :=
  { (adjoin R s).toRing, adjoinCommSemiringOfComm R hcomm with }
#align algebra.adjoin_comm_ring_of_comm Algebra.adjoinCommRingOfComm