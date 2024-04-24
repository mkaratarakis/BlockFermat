def RingEquiv.piFinTwo (R : Fin 2 → Type*) [∀ i, Semiring (R i)] :
    (∀ i : Fin 2, R i) ≃+* R 0 × R 1 :=
  { piFinTwoEquiv R with
    toFun := piFinTwoEquiv R
    map_add' := fun _ _ => rfl
    map_mul' := fun _ _ => rfl }
#align ring_equiv.pi_fin_two RingEquiv.piFinTwo