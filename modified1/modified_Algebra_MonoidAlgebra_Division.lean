def divOf (x : k[G]) (g : G) : k[G] :=
  -- note: comapping by `+ g` has the effect of subtracting `g` from every element in
  -- the support, and discarding the elements of the support from which `g` can't be subtracted.
  -- If `G` is an additive group, such as `ℤ` when used for `LaurentPolynomial`,
  -- then no discarding occurs.
  @Finsupp.comapDomain.addMonoidHom _ _ _ _ (g + ·) (add_right_injective g) x
#align add_monoid_algebra.div_of AddMonoidAlgebra.divOf

def divOfHom : Multiplicative G →* AddMonoid.End k[G] where
  toFun g :=
    { toFun := fun x => divOf x (Multiplicative.toAdd g)
      map_zero' := zero_divOf _
      map_add' := fun x y => add_divOf x y (Multiplicative.toAdd g) }
  map_one' := AddMonoidHom.ext divOf_zero
  map_mul' g₁ g₂ :=
    AddMonoidHom.ext fun _x =>
      (congr_arg _ (add_comm (Multiplicative.toAdd g₁) (Multiplicative.toAdd g₂))).trans
        (divOf_add _ _ _)
#align add_monoid_algebra.div_of_hom AddMonoidAlgebra.divOfHom

def modOf (x : k[G]) (g : G) : k[G] :=
  letI := Classical.decPred fun g₁ => ∃ g₂, g₁ = g + g₂
  x.filter fun g₁ => ¬∃ g₂, g₁ = g + g₂
#align add_monoid_algebra.mod_of AddMonoidAlgebra.modOf