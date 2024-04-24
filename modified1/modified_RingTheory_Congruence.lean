def ringConGen [Add R] [Mul R] (r : R → R → Prop) : RingCon R where
  r := RingConGen.Rel r
  iseqv := ⟨RingConGen.Rel.refl, @RingConGen.Rel.symm _ _ _ _, @RingConGen.Rel.trans _ _ _ _⟩
  add' := RingConGen.Rel.add
  mul' := RingConGen.Rel.mul
#align ring_con_gen ringConGen

def Quotient :=
  Quotient c.toSetoid
#align ring_con.quotient RingCon.Quotient

def toQuotient (r : R) : c.Quotient :=
  @Quotient.mk'' _ c.toSetoid r

variable (c)

/-- Coercion from a type with addition and multiplication to its quotient by a congruence relation.

See Note [use has_coe_t]. -/
instance : CoeTC R c.Quotient :=
  ⟨toQuotient⟩

-- Lower the priority since it unifies with any quotient type.
/-- The quotient by a decidable congruence relation has decidable equality. -/
instance (priority := 500) [_d : ∀ a b, Decidable (c a b)] : DecidableEq c.Quotient :=
  inferInstanceAs (DecidableEq (Quotient c.toSetoid))

@[simp]
theorem quot_mk_eq_coe (x : R) : Quot.mk c x = (x : c.Quotient) :=
  rfl
#align ring_con.quot_mk_eq_coe RingCon.quot_mk_eq_coe

def mk' [NonAssocSemiring R] (c : RingCon R) : R →+* c.Quotient
    where
  toFun := toQuotient
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
#align ring_con.mk' RingCon.mk'

structure RingCon (R : Type*) [Add R] [Mul R] extends Con R, AddCon R where
#align ring_con RingCon

structure

The operations above on the quotient by `c : RingCon R` preserve the algebraic structure of `R`.
-/


section Algebraic

instance [NonUnitalNonAssocSemiring R] (c : RingCon R) : NonUnitalNonAssocSemiring c.Quotient :=
  Function.Surjective.nonUnitalNonAssocSemiring _ Quotient.surjective_Quotient_mk'' rfl
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

instance [NonAssocSemiring R] (c : RingCon R) : NonAssocSemiring c.Quotient :=
  Function.Surjective.nonAssocSemiring _ Quotient.surjective_Quotient_mk'' rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl

instance [NonUnitalSemiring R] (c : RingCon R) : NonUnitalSemiring c.Quotient :=
  Function.Surjective.nonUnitalSemiring _ Quotient.surjective_Quotient_mk'' rfl (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

instance [Semiring R] (c : RingCon R) : Semiring c.Quotient :=
  Function.Surjective.semiring _ Quotient.surjective_Quotient_mk'' rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl

instance [CommSemiring R] (c : RingCon R) : CommSemiring c.Quotient :=
  Function.Surjective.commSemiring _ Quotient.surjective_Quotient_mk'' rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl

instance [NonUnitalNonAssocRing R] (c : RingCon R) : NonUnitalNonAssocRing c.Quotient :=
  Function.Surjective.nonUnitalNonAssocRing _ Quotient.surjective_Quotient_mk'' rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

instance [NonAssocRing R] (c : RingCon R) : NonAssocRing c.Quotient :=
  Function.Surjective.nonAssocRing _ Quotient.surjective_Quotient_mk'' rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) fun _ => rfl

instance [NonUnitalRing R] (c : RingCon R) : NonUnitalRing c.Quotient :=
  Function.Surjective.nonUnitalRing _ Quotient.surjective_Quotient_mk'' rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

instance [Ring R] (c : RingCon R) : Ring c.Quotient :=
  Function.Surjective.ring _ Quotient.surjective_Quotient_mk'' rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) fun _ => rfl

instance [CommRing R] (c : RingCon R) : CommRing c.Quotient :=
  Function.Surjective.commRing _ Quotient.surjective_Quotient_mk'' rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) fun _ => rfl

instance isScalarTower_right [Add R] [MulOneClass R] [SMul α R] [IsScalarTower α R R]
    (c : RingCon R) : IsScalarTower α c.Quotient c.Quotient where
  smul_assoc _ := Quotient.ind₂' fun _ _ => congr_arg Quotient.mk'' <| smul_mul_assoc _ _ _
#align ring_con.is_scalar_tower_right RingCon.isScalarTower_right